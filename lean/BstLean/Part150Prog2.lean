import BstLean.Part150Prog

/-!
# Part 150, item 4: the arithmetic pass over `A` as one straight-line program

Role: `delegations/statements/p150-spec.md`, item 4. Paper source: `onW45-opus-prover.md` §1
(the program `P45`, stages (S), (A0)–(A4)) and §6 (the count), `onW45c-cx.md` §§1, 7.

The program is a list of 41 stages over the named variables `PV n m J` (tools: `Part150Prog`).
`n`: the dimension; `m`: the hidden width of `A`; `J`: the atom count (one count for both
layers, as the main form of the paper). Inputs (`PIn n m`): the entries of the centre `c = ĉ`,
the scalar `τ = τ_0`, the entries of `A₁`, `A₂`, `A₃`.

* (S) `pS`: `ι = 1/√J`, `z_l = (2l − J)·ι`.
* (A0) `pA0`: `τ²`, `ρ² = |c|² + nτ²`, `ρ`.
* (A1) `pA1a`, `pA1b`, `pA1`: for each row of `A₁`: `m_i`, `q_i = |r_i|²`, `s_i = τ√q_i`,
  `x_i = m_i/s_i`; for each atom `ϱ = relu(x_i + z_l)`, `w = p_l ϱ`, `w′ = wϱ`; `α_i = Σ w`,
  `β_i = Σ w′`; `h̃_i = s_i α_i`, `g_i = (τ² q_i) β_i`.
* (A2) `pA2`: `G = Σ g_i`, `H = Σ h̃_i²`, `s̃² = (2/m)(G − H)`, `s̃`, `d_l = s̃ z_l`.
* (A3) `pA3`: `ã = A₂ h̃`, `b̃′_j = Σ_l p_l relu(ã_j + d_l)`.
* (A4) `passAll`: `ν = |b̃′|²`, `A₃ b̃′`, `c̃_A = (A₃ b̃′)/ρ`,
  `σ̃_p = √(relu(2/n − (2/m)ν/ρ²))`.
* `passProg`: the outputs `c̃_A` (`inl i`) and `σ̃_p` (`inr ()`).
* `passAllZ`, `passProgZ`: the same with the zero factor `ζ` of the paper as a third output.
The value lemmas and the count are in `Part150Prog3`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open BstLean.Cost
open BstLean.Part130 BstLean.Part140

noncomputable section

/-- The named variables of the pass over `A`. -/
inductive PV (n m J : ℕ) : Type
  | c (j : Fin n) | tau | A1 (i : Fin m) (j : Fin n) | A2 (i j : Fin m) | A3 (i : Fin n) (j : Fin m)
  | rJ | iota | z (l : Fin (J + 1))
  | tau2 | cc | ntau | rho2 | rho
  | mm (i : Fin m) | q (i : Fin m) | nr (i : Fin m) | s (i : Fin m) | x (i : Fin m)
  | y (i : Fin m) (l : Fin (J + 1)) | r (i : Fin m) (l : Fin (J + 1))
  | w (i : Fin m) (l : Fin (J + 1)) | w2 (i : Fin m) (l : Fin (J + 1))
  | al (i : Fin m) | be (i : Fin m) | h (i : Fin m) | tq (i : Fin m) | g (i : Fin m) | G | H
  | GH | st2 | st | d (l : Fin (J + 1))
  | a (i : Fin m) | u (i : Fin m) (l : Fin (J + 1)) | ru (i : Fin m) (l : Fin (J + 1))
  | wu (i : Fin m) (l : Fin (J + 1)) | b (i : Fin m) | nu
  | e (i : Fin n) | cT (i : Fin n) | tnu | f | gm | rg | sig
  | zt | zs | zn | zts | zeta

variable (n m J : ℕ)

/-- The inputs: the entries of `c`, the scalar `τ`, the entries of `A₁`, `A₂`, `A₃`. -/
abbrev PIn : Type := Fin n ⊕ Unit ⊕ (Fin m × Fin n) ⊕ (Fin m × Fin m) ⊕ (Fin n × Fin m)

variable {n m}

/-- The inputs as one valuation. -/
def passVal (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) : PIn n m → ℝ :=
  Sum.elim c (Sum.elim (fun _ => τ) (Sum.elim (fun e => A₁ e.1 e.2)
    (Sum.elim (fun e => A₂ e.1 e.2) (fun e => A₃ e.1 e.2))))

variable (n m)

/-- The rational binomial weight `C(J, l)/2^J`. -/
def pQ (l : ℕ) : ℚ := (J.choose l : ℚ) / 2 ^ J

/-- The start: the input variables read the inputs; every other variable reads `0`. -/
def p0 : RProg (PIn n m) (PV n m J) :=
  RProg.args fun x => match x with
    | .c j => .inp (Sum.inl j)
    | .tau => .inp (Sum.inr (Sum.inl ()))
    | .A1 i j => .inp (Sum.inr (Sum.inr (Sum.inl (i, j))))
    | .A2 i j => .inp (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))
    | .A3 i j => .inp (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j)))))
    | _ => .cst 0

/-- Stage (S): `ι = 1/√J`, `z_l = (2l − J)·ι`. `J + 3` operations. -/
def pS : RProg (PIn n m) (PV n m J) :=
  (((p0 n m J).stage
    (op1Stage (κ := Unit) .sqrt (fun _ => .cst J) (fun _ => .cst J))
      (fun x => match x with | .rJ => some () | _ => none)).stage
    (op1Stage (κ := Unit) .div (fun _ => .cst 1) (fun _ => .inp .rJ))
      (fun x => match x with | .iota => some () | _ => none)).stage
    (op1Stage (κ := Fin (J + 1)) .mul (fun l => .cst (2 * (l : ℕ) - J)) (fun _ => .inp .iota))
      (fun x => match x with | .z l => some l | _ => none)


/-- Stage (A0): `τ²`, `|c|²`, `nτ²`, `ρ²`, `ρ`. `2n + 3` operations (for `n ≥ 1`). -/
def pA0 : RProg (PIn n m) (PV n m J) :=
  (((((pS n m J).stage
    (op1Stage (κ := Unit) .mul (fun _ => .inp .tau) (fun _ => .inp .tau))
      (fun x => match x with | .tau2 => some () | _ => none)).stage
    (dotStage (κ := Unit) n (fun _ j => .c j) (fun _ j => .c j))
      (fun x => match x with | .cc => some () | _ => none)).stage
    (op1Stage (κ := Unit) .mul (fun _ => .cst n) (fun _ => .inp .tau2))
      (fun x => match x with | .ntau => some () | _ => none)).stage
    (op1Stage (κ := Unit) .add (fun _ => .inp .cc) (fun _ => .inp .ntau))
      (fun x => match x with | .rho2 => some () | _ => none)).stage
    (op1Stage (κ := Unit) .sqrt (fun _ => .inp .rho2) (fun _ => .inp .rho2))
      (fun x => match x with | .rho => some () | _ => none)

/-- Stage (A1), first part: `m_i`, `q_i`, `|r_i|`, `s_i`, `x_i = m_i/s_i` for each row. -/
def pA1a : RProg (PIn n m) (PV n m J) :=
  (((((pA0 n m J).stage
    (dotStage (κ := Fin m) n (fun i j => .A1 i j) (fun _ j => .c j))
      (fun x => match x with | .mm i => some i | _ => none)).stage
    (dotStage (κ := Fin m) n (fun i j => .A1 i j) (fun i j => .A1 i j))
      (fun x => match x with | .q i => some i | _ => none)).stage
    (op1Stage (κ := Fin m) .sqrt (fun i => .inp (.q i)) (fun i => .inp (.q i)))
      (fun x => match x with | .nr i => some i | _ => none)).stage
    (op1Stage (κ := Fin m) .mul (fun _ => .inp .tau) (fun i => .inp (.nr i)))
      (fun x => match x with | .s i => some i | _ => none)).stage
    (op1Stage (κ := Fin m) .div (fun i => .inp (.mm i)) (fun i => .inp (.s i)))
      (fun x => match x with | .x i => some i | _ => none)

/-- Stage (A1), the atoms: `ϱ = relu(x_i + z_l)`, `w = p_l ϱ`, `w′ = w ϱ`, `α_i`, `β_i`. -/
def pA1b : RProg (PIn n m) (PV n m J) :=
  ((((((pA1a n m J).stage
    (op1Stage (κ := Fin m × Fin (J + 1)) .add (fun k => .inp (.x k.1)) (fun k => .inp (.z k.2)))
      (fun x => match x with | .y i l => some (i, l) | _ => none)).stage
    (op1Stage (κ := Fin m × Fin (J + 1)) .relu (fun k => .inp (.y k.1 k.2))
        (fun k => .inp (.y k.1 k.2)))
      (fun x => match x with | .r i l => some (i, l) | _ => none)).stage
    (op1Stage (κ := Fin m × Fin (J + 1)) .mul (fun k => .cst (pQ J k.2))
        (fun k => .inp (.r k.1 k.2)))
      (fun x => match x with | .w i l => some (i, l) | _ => none)).stage
    (op1Stage (κ := Fin m × Fin (J + 1)) .mul (fun k => .inp (.w k.1 k.2))
        (fun k => .inp (.r k.1 k.2)))
      (fun x => match x with | .w2 i l => some (i, l) | _ => none)).stage
    (sumStage (κ := Fin m) (J + 1) (fun i l => .w i l))
      (fun x => match x with | .al i => some i | _ => none)).stage
    (sumStage (κ := Fin m) (J + 1) (fun i l => .w2 i l))
      (fun x => match x with | .be i => some i | _ => none)

/-- Stage (A1), the end: `h̃_i = s_i α_i`, `τ² q_i`, `g_i = (τ² q_i) β_i`. -/
def pA1 : RProg (PIn n m) (PV n m J) :=
  (((pA1b n m J).stage
    (op1Stage (κ := Fin m) .mul (fun i => .inp (.s i)) (fun i => .inp (.al i)))
      (fun x => match x with | .h i => some i | _ => none)).stage
    (op1Stage (κ := Fin m) .mul (fun _ => .inp .tau2) (fun i => .inp (.q i)))
      (fun x => match x with | .tq i => some i | _ => none)).stage
    (op1Stage (κ := Fin m) .mul (fun i => .inp (.tq i)) (fun i => .inp (.be i)))
      (fun x => match x with | .g i => some i | _ => none)

/-- The sums of (A1) and stage (A2): `G = Σ g_i`, `H = Σ h̃_i²`, `G − H`,
`s̃² = (2/m)(G − H)`, `s̃`, `d_l = s̃ z_l`. -/
def pA2 : RProg (PIn n m) (PV n m J) :=
  ((((((pA1 n m J).stage
    (sumStage (κ := Unit) m (fun _ i => .g i))
      (fun x => match x with | .G => some () | _ => none)).stage
    (dotStage (κ := Unit) m (fun _ i => .h i) (fun _ i => .h i))
      (fun x => match x with | .H => some () | _ => none)).stage
    (op1Stage (κ := Unit) .sub (fun _ => .inp .G) (fun _ => .inp .H))
      (fun x => match x with | .GH => some () | _ => none)).stage
    (op1Stage (κ := Unit) .mul (fun _ => .cst (2 / (m : ℚ))) (fun _ => .inp .GH))
      (fun x => match x with | .st2 => some () | _ => none)).stage
    (op1Stage (κ := Unit) .sqrt (fun _ => .inp .st2) (fun _ => .inp .st2))
      (fun x => match x with | .st => some () | _ => none)).stage
    (op1Stage (κ := Fin (J + 1)) .mul (fun _ => .inp .st) (fun l => .inp (.z l)))
      (fun x => match x with | .d l => some l | _ => none)

/-- Stage (A3): `ã = A₂ h̃`, `b̃′_j = Σ_l p_l relu(ã_j + d_l)`. -/
def pA3 : RProg (PIn n m) (PV n m J) :=
  (((((pA2 n m J).stage
    (dotStage (κ := Fin m) m (fun i j => .A2 i j) (fun _ j => .h j))
      (fun x => match x with | .a i => some i | _ => none)).stage
    (op1Stage (κ := Fin m × Fin (J + 1)) .add (fun k => .inp (.a k.1)) (fun k => .inp (.d k.2)))
      (fun x => match x with | .u i l => some (i, l) | _ => none)).stage
    (op1Stage (κ := Fin m × Fin (J + 1)) .relu (fun k => .inp (.u k.1 k.2))
        (fun k => .inp (.u k.1 k.2)))
      (fun x => match x with | .ru i l => some (i, l) | _ => none)).stage
    (op1Stage (κ := Fin m × Fin (J + 1)) .mul (fun k => .cst (pQ J k.2))
        (fun k => .inp (.ru k.1 k.2)))
      (fun x => match x with | .wu i l => some (i, l) | _ => none)).stage
    (sumStage (κ := Fin m) (J + 1) (fun i l => .wu i l))
      (fun x => match x with | .b i => some i | _ => none)

/-- `ν = |b̃′|²` and stage (A4): `A₃ b̃′`, `c̃_A = (A₃ b̃′)/ρ`, `(2/m)ν`, `/ρ²`, `2/n − ·`,
`relu`, `√`. -/
def passAll : RProg (PIn n m) (PV n m J) :=
  ((((((((pA3 n m J).stage
    (dotStage (κ := Unit) m (fun _ i => .b i) (fun _ i => .b i))
      (fun x => match x with | .nu => some () | _ => none)).stage
    (dotStage (κ := Fin n) m (fun i j => .A3 i j) (fun _ j => .b j))
      (fun x => match x with | .e i => some i | _ => none)).stage
    (op1Stage (κ := Fin n) .div (fun i => .inp (.e i)) (fun _ => .inp .rho))
      (fun x => match x with | .cT i => some i | _ => none)).stage
    (op1Stage (κ := Unit) .mul (fun _ => .cst (2 / (m : ℚ))) (fun _ => .inp .nu))
      (fun x => match x with | .tnu => some () | _ => none)).stage
    (op1Stage (κ := Unit) .div (fun _ => .inp .tnu) (fun _ => .inp .rho2))
      (fun x => match x with | .f => some () | _ => none)).stage
    (op1Stage (κ := Unit) .sub (fun _ => .cst (2 / (n : ℚ))) (fun _ => .inp .f))
      (fun x => match x with | .gm => some () | _ => none)).stage
    (op1Stage (κ := Unit) .relu (fun _ => .inp .gm) (fun _ => .inp .gm))
      (fun x => match x with | .rg => some () | _ => none)).stage
    (op1Stage (κ := Unit) .sqrt (fun _ => .inp .rg) (fun _ => .inp .rg))
      (fun x => match x with | .sig => some () | _ => none)

/-- **The arithmetic pass over `A`**: from the entries of `c`, `τ`, `A₁`, `A₂`, `A₃` to
`c̃_A` (outputs `inl i`) and `σ̃_p` (output `inr ()`). Operations `+ − × ÷ √ relu` and rational
constants only; no oracle; no vector `A(x)` is computed. -/
def passProg : RProg (PIn n m) (Fin n ⊕ Unit) :=
  (passAll n m J).mapOut (Sum.elim PV.cT (fun _ => PV.sig))

/-- The zero factor `ζ = (τ²/τ²)·(s̃²/s̃²)·(ν/ν)` (5 operations; total division `x/0 = 0`):
`ζ = 0` when `τ = 0`, `s̃² = 0` or `b̃′ = 0`, and `ζ = 1` otherwise. -/
def passAllZ : RProg (PIn n m) (PV n m J) :=
  (((((passAll n m J).stage
    (op1Stage (κ := Unit) .div (fun _ => .inp .tau2) (fun _ => .inp .tau2))
      (fun x => match x with | .zt => some () | _ => none)).stage
    (op1Stage (κ := Unit) .div (fun _ => .inp .st2) (fun _ => .inp .st2))
      (fun x => match x with | .zs => some () | _ => none)).stage
    (op1Stage (κ := Unit) .div (fun _ => .inp .nu) (fun _ => .inp .nu))
      (fun x => match x with | .zn => some () | _ => none)).stage
    (op1Stage (κ := Unit) .mul (fun _ => .inp .zt) (fun _ => .inp .zs))
      (fun x => match x with | .zts => some () | _ => none)).stage
    (op1Stage (κ := Unit) .mul (fun _ => .inp .zts) (fun _ => .inp .zn))
      (fun x => match x with | .zeta => some () | _ => none)

/-- The pass over `A` with the zero factor: outputs `c̃_A` (`inl i`), `σ̃_p` (`inr (inl ())`)
and `ζ` (`inr (inr ())`). -/
def passProgZ : RProg (PIn n m) (Fin n ⊕ Unit ⊕ Unit) :=
  (passAllZ n m J).mapOut (Sum.elim PV.cT (Sum.elim (fun _ => PV.sig) (fun _ => PV.zeta)))

end

end BstLean.Part150
