import BstLean.Part141Centre
import BstLean.Part141Atom2
import BstLean.Part141Shift
import BstLean.Part140Prog

/-!
# Part 141: the rational constants, the arithmetic centre `b̃`, the arithmetic scalar `τ̃₀`, and
the comparison with the computed centre `b̂` and the scalar `τ̂₀` of Part 140

Role: `delegations/statements/p141-spec.md`, items 1 to 3. Paper sources: `onW8c-cx.md` §§2–3,
`onW17c-cx.md` §§4–5 (the route here is a perturbation from Part 140, not Lemma H2′).

The constants (they depend on `n` only; all are rational numbers):
* `qA n = 10000·n` (the accuracy parameter), `hA n = ⌊√(4·qA n)⌋ + 1` (the cells have mesh
  `1/hA n`), `RA n = ⌈log₂(32·qA n)⌉` (the atoms are in `[−RA n, RA n]`),
  `LA n = 2·RA n·hA n + 1` (the number of atoms), `DA n` (the denominator of the weights),
  `zA n`, `pA n`: the atoms (rounded conditional means of the cells, `Part141Atom2`) and the
  weights.
* `cA n = ⌊D·c_N⌋/D` with `D = DcA n = 2n·(qA n)²`: the rational replacement of `c_N`.
* `c1A n = ⌊q·c₁⌋/q` with `q = qA n`: the rational replacement of `c₁ = 1/(γκ₁²)`.

* **`atomErrA`** (item 1): `|ψ̃(x) − ψ_s(x)| ≤ s·3/qA n` for every `s ≥ 0`, `x`.
* `cA_le`, `cA_ge`, `c1A_err`: the errors of the rational constants.
* `bA n θ`: the arithmetic centre; `tauA n θ`: the arithmetic scalar; `dA n θ = t|b̃ − b̂|²`.
* **`centreArith141`** (item 2): `E_θ t|b̃ − b̂|² ≤ γ·68/(qA n)²`.
* `goodA n = goodHat n ∩ {t|b̃ − b̂|² ≤ γ/10⁶}`; `goodA_prob`.
* `tauN`, `scalarA`: on `goodA n`: `τ̃₀² ≥ 0.458·γ`, `τ̂₀² ≥ 0.46·γ` and
  `(τ̃₀² − τ̂₀²)² ≤ γ²·(42·X + 3/q²)`, `X = t|b̃ − b̂|²/γ`.
* **`KA_le`**: on `goodA n`: `8·hellG n τ̃₀ τ̂₀ + 2n·t|b̃ − b̂|²/τ̃₀² ≤ n·(404·X + 29/q²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part138 BstLean.Part140

/-! ## Two facts on real numbers and vectors -/

lemma sq_add2 (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The scalar in normalized units: `β = t|b̂|²/γ`, `β′ = t|b̃|²/γ`, `κ = γc₁`, `κ′ = γc̃₁`,
`ξ = t|b̃ − b̂|²/γ`. -/
lemma tauN {β β' κ κ' ξ e : ℝ} (h1 : 48 / 100 ≤ β) (h2 : β ≤ 508 / 1000) (h0 : 0 ≤ β')
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 1000000) (hd : (β' - β) ^ 2 ≤ 2 * ξ * (β' + β))
    (hκ1 : 4101 / 1000 ≤ κ) (hκ2 : κ ≤ 41025 / 10000) (hκ' : |κ' - κ| ≤ e * κ) (he0 : 0 ≤ e)
    (he : e ≤ 1 / 1000) :
    46 / 100 ≤ β * relu (β * κ - 1) ∧ 458 / 1000 ≤ β' * relu (β' * κ' - 1) ∧
      (β' * relu (β' * κ' - 1) - β * relu (β * κ - 1)) ^ 2 ≤ 42 * ξ + 3 * e ^ 2 := by
  have hβ0 : 0 ≤ β := by linarith
  have hsum0 : 0 ≤ β' + β := by linarith
  have hb : 2 * ξ * (β' + β) ≤ 2 * (1 / 1000000) * (β' + β) := by nlinarith
  have hΔu : β' - β ≤ 15 / 10000 := by
    by_contra h
    push Not at h
    nlinarith
  have hΔl : -(15 / 10000) ≤ β' - β := by
    by_contra h
    push Not at h
    nlinarith
  have hΔ2 : (β' - β) ^ 2 ≤ 2035 / 1000 * ξ := by nlinarith
  set d : ℝ := |β' - β| with hdd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hdle : d ≤ 15 / 10000 := abs_le.mpr ⟨hΔl, hΔu⟩
  have hdsq : d ^ 2 = (β' - β) ^ 2 := sq_abs _
  obtain ⟨hk1, hk2⟩ := abs_le.mp hκ'
  have heκ : e * κ ≤ 41025 / 10000000 := by nlinarith
  have hκ'0 : 0 ≤ κ' := by linarith
  have hκ'u : κ' ≤ 4107 / 1000 := by linarith
  set u : ℝ := β * κ - 1 with hu
  set u' : ℝ := β' * κ' - 1 with hu'
  have hul : 96848 / 100000 ≤ u := by rw [hu]; nlinarith
  have huu : u ≤ 108407 / 100000 := by rw [hu]; nlinarith
  have hdu : |u' - u| ≤ 4107 / 1000 * d + 20841 / 10000 * e := by
    have e1 : u' - u = (β' - β) * κ' + β * (κ' - κ) := by rw [hu, hu']; ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hκ'0, abs_of_nonneg hβ0]
    have a1 : d * κ' ≤ d * (4107 / 1000) := mul_le_mul_of_nonneg_left hκ'u hd0
    have a2 : β * |κ' - κ| ≤ 508 / 1000 * (e * (41025 / 10000)) :=
      mul_le_mul h2 (hκ'.trans (mul_le_mul_of_nonneg_left hκ2 he0)) (abs_nonneg _)
        (by norm_num)
    linarith
  obtain ⟨hdu1, hdu2⟩ := abs_le.mp hdu
  have hu'l : 96 / 100 ≤ u' := by linarith
  have hu'u : u' ≤ 10924 / 10000 := by linarith
  have er : relu u = u := relu_of_nonneg (by linarith)
  have er' : relu u' = u' := relu_of_nonneg (by linarith)
  rw [er, er']
  have hD : |β' * u' - β * u| ≤ 318 / 100 * d + 106 / 100 * e := by
    have e1 : β' * u' - β * u = (β' - β) * u' + β * (u' - u) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u'), abs_of_nonneg hβ0]
    have a1 : d * u' ≤ d * (10924 / 10000) := mul_le_mul_of_nonneg_left hu'u hd0
    have a2 : β * |u' - u| ≤ 508 / 1000 * (4107 / 1000 * d + 20841 / 10000 * e) :=
      mul_le_mul h2 hdu (abs_nonneg _) (by norm_num)
    linarith
  obtain ⟨hD1, hD2⟩ := abs_le.mp hD
  have hβu : 48 / 100 * (96848 / 100000) ≤ β * u := mul_le_mul h1 hul (by norm_num) hβ0
  refine ⟨by linarith, by linarith, ?_⟩
  have hsq : (β' * u' - β * u) ^ 2 ≤ (318 / 100 * d + 106 / 100 * e) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hD 2
  have h3 := sq_add2 (318 / 100 * d) (106 / 100 * e)
  have h4 : (318 / 100 * d) ^ 2 = (318 / 100) ^ 2 * (β' - β) ^ 2 := by rw [mul_pow, hdsq]
  have h5 : (106 / 100 * e) ^ 2 = (106 / 100) ^ 2 * e ^ 2 := by rw [mul_pow]
  rw [h4, h5] at h3
  have h6 : (318 / 100 : ℝ) ^ 2 * (β' - β) ^ 2 ≤ (318 / 100) ^ 2 * (2035 / 1000 * ξ) :=
    mul_le_mul_of_nonneg_left hΔ2 (by norm_num)
  have h7 : 0 ≤ e ^ 2 := sq_nonneg e
  norm_num at h3 h6
  linarith

/-- `(|a|² − |b|²)² ≤ 2·|a − b|²·(|a|² + |b|²)`. -/
lemma normSq_diff_sq {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (normSq a - normSq b) ^ 2 ≤ 2 * normSq (a - b) * (normSq a + normSq b) := by
  have e : normSq a - normSq b = ∑ i, (a i - b i) * (a i + b i) := by
    unfold normSq
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => a i - b i)
    (fun i => a i + b i)
  have h2 : ∑ i, (a i + b i) ^ 2 ≤ 2 * (normSq a + normSq b) := by
    unfold normSq
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (a i - b i)]
  have h3 : ∑ i, (a i - b i) ^ 2 = normSq (a - b) := rfl
  rw [e]
  rw [h3] at cs
  have h4 := mul_le_mul_of_nonneg_left h2 (normSq_nonneg (a - b))
  calc (∑ i, (a i - b i) * (a i + b i)) ^ 2 ≤ normSq (a - b) * ∑ i, (a i + b i) ^ 2 := cs
    _ ≤ normSq (a - b) * (2 * (normSq a + normSq b)) := h4
    _ = _ := by ring

/-- `(a − b)²/(a² + b²) ≤ (a² − b²)²/(a² + b²)²` for `a ≥ 0`, `b > 0`. -/
lemma hell_frac {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (a - b) ^ 2 / (a ^ 2 + b ^ 2) ≤ (a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 + b ^ 2) ^ 2 := by
  have hpos : 0 < a ^ 2 + b ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have e : (a ^ 2 - b ^ 2) ^ 2 = (a - b) ^ 2 * (a + b) ^ 2 := by ring
  rw [e]
  have h1 : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [mul_nonneg ha hb.le]
  calc (a - b) ^ 2 * (a ^ 2 + b ^ 2) ^ 2 = ((a - b) ^ 2 * (a ^ 2 + b ^ 2)) * (a ^ 2 + b ^ 2) := by
        ring
    _ ≤ ((a - b) ^ 2 * (a + b) ^ 2) * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) hpos.le

/-- The numbers of `KA_le`. -/
lemma K_num {T T' ξ e : ℝ} (hT : 46 / 100 ≤ T) (hT' : 458 / 1000 ≤ T') (hξ : 0 ≤ ξ)
    (hD : (T' - T) ^ 2 ≤ 42 * ξ + 3 * e ^ 2) :
    8 * ((T' - T) ^ 2 / (T' + T) ^ 2) + 2 * ξ / T' ≤ 404 * ξ + 29 * e ^ 2 := by
  have hs : (918 / 1000 : ℝ) ≤ T' + T := by linarith
  have hs2 : (842724 / 1000000 : ℝ) ≤ (T' + T) ^ 2 := by nlinarith
  have h1 : (T' - T) ^ 2 / (T' + T) ^ 2 ≤ (42 * ξ + 3 * e ^ 2) / (842724 / 1000000) := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have h0 : 0 ≤ (T' - T) ^ 2 := sq_nonneg _
    have h00 : 0 ≤ 42 * ξ + 3 * e ^ 2 := by positivity
    nlinarith
  have h2 : 2 * ξ / T' ≤ 2 * ξ / (458 / 1000) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hT'
  have e1 : (42 * ξ + 3 * e ^ 2) / (842724 / 1000000) =
      (42 * ξ + 3 * e ^ 2) * (1000000 / 842724) := by field_simp
  have e2 : 2 * ξ / (458 / 1000) = 2 * ξ * (1000 / 458) := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  nlinarith [sq_nonneg e]

/-! ## The rational constants -/

/-- The accuracy parameter: the finite ReLU sum is within `s·3/qA n` of `ψ_s`. -/
def qA (n : ℕ) : ℕ := 10000 * n

/-- The inverse mesh of the cells: `hA n = ⌊√(4·qA n)⌋ + 1`, so `(hA n)² ≥ 4·qA n`. -/
def hA (n : ℕ) : ℕ := Nat.sqrt (4 * qA n) + 1

/-- The range of the atoms: `[−RA n, RA n]`, with `2^{RA n} ≥ 32·qA n`. -/
def RA (n : ℕ) : ℕ := Nat.clog 2 (32 * qA n)

/-- The denominator of the weights. -/
def DA (n : ℕ) : ℕ := 4 * (RA n + 1) ^ 2 * hA n * qA n

/-- The number of atoms. -/
abbrev LA (n : ℕ) : ℕ := 2 * RA n * hA n + 1

/-- The denominator of the rational replacement of `c_N`. -/
def DcA (n : ℕ) : ℕ := 2 * n * qA n ^ 2

/-- **The rational replacement of `c_N`**, `N = 2n`: `⌊D·c_N⌋/D`, `D = DcA n`. -/
noncomputable def cA (n : ℕ) : ℚ := ((⌊(DcA n : ℝ) * cN (2 * n)⌋ : ℤ) : ℚ) / (DcA n : ℚ)

/-- **The rational replacement of `c₁ = 1/(γκ₁²)`**: `⌊q·c₁⌋/q`, `q = qA n`. -/
noncomputable def c1A (n : ℕ) : ℚ := ((⌊(qA n : ℝ) * c1Hat (2 * n)⌋ : ℤ) : ℚ) / (qA n : ℚ)

/-- The rational atoms: the conditional means of the cells, rounded down to multiples of
`1/qA n` (`zM` of `Part141Atom2`). -/
noncomputable def zA (n : ℕ) : Fin (LA n) → ℚ := zM (hA n) (RA n) (qA n)

/-- The rational weights. -/
noncomputable def pA (n : ℕ) : Fin (LA n) → ℚ := pQ (hA n) (RA n) (DA n)

section consts

variable {n : ℕ} (hn : 1 ≤ n)

include hn

lemma qA_pos : 1 ≤ qA n := by unfold qA; omega

omit hn in
lemma qA_cast : (qA n : ℝ) = 10000 * (n : ℝ) := by unfold qA; push_cast; ring

omit hn in
lemma hA_pos : 1 ≤ hA n := by unfold hA; omega

omit hn in
lemma hA_sq : 4 * qA n ≤ hA n ^ 2 := by
  unfold hA
  have := Nat.lt_succ_sqrt (4 * qA n)
  rw [pow_two]
  exact this.le

omit hn in
lemma RA_pow : 32 * qA n ≤ 2 ^ RA n := Nat.le_pow_clog (by norm_num) _

lemma RA_pos : 1 ≤ RA n := by
  unfold RA
  exact Nat.clog_pos (by norm_num) (by have := qA_pos hn; omega)

lemma DA_pos : 1 ≤ DA n := by
  unfold DA
  have h2 := qA_pos hn
  have h3 := hA_pos (n := n)
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma DcA_pos : 1 ≤ DcA n := by
  unfold DcA
  have h2 := qA_pos hn
  have : 1 ≤ n * qA n ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  nlinarith

omit hn in
lemma DcA_cast : (DcA n : ℝ) = ((2 * n : ℕ) : ℝ) * (qA n : ℝ) ^ 2 := by
  unfold DcA; push_cast; ring

/-- **Item 1 (`atomSum141` at the constants of the program).** For every `s ≥ 0` and `x`:
`|Σ_ℓ p_ℓ·relu(x + s·z_ℓ) − ψ_s(x)| ≤ s·3/qA n`, with the rational atoms `zA n` and the rational
weights `pA n`. -/
theorem atomErrA (s x : ℝ) (hs : 0 ≤ s) :
    |atomSum (fun ℓ => ((pA n ℓ : ℚ) : ℝ)) (fun ℓ => ((zA n ℓ : ℚ) : ℝ)) s x - psiS s x| ≤
      s * (3 / (qA n : ℝ)) := by
  have hq := qA_pos hn
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast hq
  have hh' : (0 : ℝ) < hA n := by exact_mod_cast hA_pos (n := n)
  have hR := RA_pos hn
  have h := atomSum2_141 (q := hA n) (R := RA n) (D := DA n) (E := qA n) (hA_pos (n := n)) hR
    (DA_pos hn) hq hs x
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hs)
  have hp : (32 : ℝ) * (qA n : ℝ) ≤ (2 : ℝ) ^ RA n := by exact_mod_cast RA_pow (n := n)
  have hsq : (4 : ℝ) * (qA n : ℝ) ≤ (hA n : ℝ) ^ 2 := by exact_mod_cast hA_sq (n := n)
  have t0 : 2 / (hA n : ℝ) ^ 2 ≤ 1 / 2 * (1 / (qA n : ℝ)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / 2 * (1 / (qA n : ℝ)) * (hA n : ℝ) ^ 2 = (hA n : ℝ) ^ 2 / (2 * (qA n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have t1 : 16 / (2 : ℝ) ^ RA n ≤ 1 / 2 * (1 / (qA n : ℝ)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / 2 * (1 / (qA n : ℝ)) * (2 : ℝ) ^ RA n = (2 : ℝ) ^ RA n / (2 * (qA n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have t2 : 4 * ((RA n : ℝ) + 1) ^ 2 * (hA n : ℝ) / (DA n : ℝ) = 1 / (qA n : ℝ) := by
    unfold DA
    push_cast
    field_simp
  rw [t2]
  have e : 3 / (qA n : ℝ) = 1 / 2 * (1 / (qA n : ℝ)) + 1 / 2 * (1 / (qA n : ℝ)) +
      1 / (qA n : ℝ) + 1 / (qA n : ℝ) := by ring
  linarith

omit hn in
lemma cA_cast : ((cA n : ℚ) : ℝ) =
    ((⌊(DcA n : ℝ) * cN (2 * n)⌋ : ℤ) : ℝ) / (DcA n : ℝ) := by
  unfold cA; push_cast; rfl

lemma cA_nonneg : 0 ≤ ((cA n : ℚ) : ℝ) := by
  rw [cA_cast]
  exact fl_nonneg (cN_nonneg _)

lemma cA_le : ((cA n : ℚ) : ℝ) ≤ cN (2 * n) := by
  rw [cA_cast]
  exact fl_le (DcA_pos hn) _

lemma cA_ge : cN (2 * n) - 1 / (DcA n : ℝ) ≤ ((cA n : ℚ) : ℝ) := by
  rw [cA_cast]
  exact fl_ge (DcA_pos hn) _

omit hn in
lemma c1A_cast : ((c1A n : ℚ) : ℝ) =
    ((⌊(qA n : ℝ) * c1Hat (2 * n)⌋ : ℤ) : ℝ) / (qA n : ℝ) := by
  unfold c1A; push_cast; rfl

/-- `|c̃₁ − c₁| ≤ 1/qA n`. -/
lemma c1A_err : |((c1A n : ℚ) : ℝ) - c1Hat (2 * n)| ≤ 1 / (qA n : ℝ) := by
  rw [c1A_cast, abs_le]
  have h1 := fl_le (qA_pos hn) (c1Hat (2 * n))
  have h2 := fl_ge (qA_pos hn) (c1Hat (2 * n))
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn
  have : (0 : ℝ) ≤ 1 / (qA n : ℝ) := by positivity
  constructor <;> linarith

end consts

/-! ## The arithmetic centre and the arithmetic scalar -/

/-- **The arithmetic centre** `b̃`: `b̃_i = Σ_ℓ p_ℓ·relu(ã_i + s̃·z_ℓ)`, with the rational
constants of this file. -/
noncomputable def bA (n : ℕ) (θ : HidParam (2 * n) (mW n)) : Fin (mW n) → ℝ :=
  bOf ((cA n : ℚ) : ℝ) (fun ℓ => ((pA n ℓ : ℚ) : ℝ)) (fun ℓ => ((zA n ℓ : ℚ) : ℝ)) θ

/-- **The arithmetic scalar** `τ̃₀`: `τ̃₀² = t|b̃|²·max(0, t|b̃|²·c̃₁ − 1)`. -/
noncomputable def tauA (n : ℕ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  tauOf (mW n) (bA n θ) ((c1A n : ℚ) : ℝ)

/-- The distance `t|b̃ − b̂|²` of the arithmetic centre to the computed centre of Part 137. -/
noncomputable def dA (n : ℕ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  2 / (mW n : ℝ) * normSq (bA n θ - bhat θ)

lemma dA_nonneg (n : ℕ) (θ : HidParam (2 * n) (mW n)) : 0 ≤ dA n θ :=
  mul_nonneg (by positivity) (normSq_nonneg _)

lemma measurable_bA (n : ℕ) : Measurable (bA n) := measurable_bOf _ _ _

lemma measurable_tauA (n : ℕ) : Measurable (tauA n) := by
  unfold tauA tauOf
  have h1 : Measurable (fun θ : HidParam (2 * n) (mW n) =>
      2 / (mW n : ℝ) * normSq (bA n θ)) :=
    (measurable_normSq.comp (measurable_bA n)).const_mul _
  exact (h1.mul (measurable_relu.comp ((h1.mul_const _).sub_const 1))).sqrt

lemma measurable_dA {n : ℕ} (hn : 1 ≤ n) : Measurable (dA n) :=
  (measurable_normSq.comp ((measurable_bA n).sub
    (measurable_bhat (by omega : 1 ≤ 2 * n)))).const_mul _

/-- **Item 2 (`centreArith141`).** For `n ≥ 4096`: the mean over `θ = (M₁, M₂)` of
`t|b̃ − b̂|²` is at most `γ·68/(qA n)²` (`γ = 2/N`, `N = 2n`, `qA n = 10000·n`). -/
theorem centreArith141 {n : ℕ} (hn : 4096 ≤ n) :
    Integrable (dA n) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, dA n θ ∂hidGauss (2 * n) (mW n) ≤
        2 / ((2 * n : ℕ) : ℝ) * (68 / (qA n : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hm' : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have hNr : (8192 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast; linarith
  have hN0 : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by linarith
  obtain ⟨hi, hb⟩ := centre_mean (N := 2 * n) (m := mW n) hN hm
    (fun ℓ => ((pA n ℓ : ℚ) : ℝ)) (fun ℓ => ((zA n ℓ : ℚ) : ℝ)) (c := ((cA n : ℚ) : ℝ))
    (ε := 3 / (qA n : ℝ)) (cA_nonneg hn1) (cA_le hn1) (atomErrA hn1)
  refine ⟨hi, hb.trans ?_⟩
  set c : ℝ := ((cA n : ℚ) : ℝ) with hc
  set q : ℝ := (qA n : ℝ) with hq
  set NN : ℝ := ((2 * n : ℕ) : ℝ) with hNN
  have hcN0 := cN_nonneg (2 * n)
  have hcN1 := cN_le_half hN
  have hδ0 : 0 ≤ cN (2 * n) - c := by have := cA_le hn1; linarith
  have hδ1 : cN (2 * n) - c ≤ 1 / (NN * q ^ 2) := by
    have := cA_ge hn1
    rw [DcA_cast] at this
    linarith
  have hD0 : (0 : ℝ) < NN * q ^ 2 := by positivity
  have hq1 : (1 : ℝ) ≤ q := by rw [hq]; exact_mod_cast qA_pos hn1
  -- the three terms
  have t1 : 6 * (3 / q) ^ 2 = 54 / q ^ 2 := by field_simp; ring
  have t2 : 24 * NN * cN (2 * n) * (cN (2 * n) - c) ≤ 12 / q ^ 2 := by
    have h1 : 24 * NN * cN (2 * n) * (cN (2 * n) - c) ≤ 24 * NN * (1 / 2) * (1 / (NN * q ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcN1 (by positivity)) hδ1 hδ0 (by positivity)
    have e : 24 * NN * (1 / 2) * (1 / (NN * q ^ 2)) = 12 / q ^ 2 := by field_simp; ring
    linarith
  have t3 : 12 * NN * (cN (2 * n) - c) ^ 2 ≤ 1 / q ^ 2 := by
    have h1 : (cN (2 * n) - c) ^ 2 ≤ (1 / (NN * q ^ 2)) ^ 2 := pow_le_pow_left₀ hδ0 hδ1 2
    have h2 : 12 * NN * (cN (2 * n) - c) ^ 2 ≤ 12 * NN * (1 / (NN * q ^ 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : 12 * NN * (1 / (NN * q ^ 2)) ^ 2 = 12 / (NN * q ^ 2) * (1 / q ^ 2) := by
      field_simp
    have h3 : 12 / (NN * q ^ 2) ≤ 1 := by
      rw [div_le_one hD0]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hq1 2]
    have h4 : (0 : ℝ) ≤ 1 / q ^ 2 := by positivity
    rw [e] at h2
    nlinarith
  have hs : √(1 + 5 / (mW n : ℝ)) ≤ 68 / 67 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have : 5 / (mW n : ℝ) ≤ 5 / 1000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
    norm_num at this ⊢
    linarith
  have hsum : 6 * (3 / q) ^ 2 + 24 * NN * cN (2 * n) * (cN (2 * n) - c) +
      12 * NN * (cN (2 * n) - c) ^ 2 ≤ 67 / q ^ 2 := by
    rw [t1]
    have e : (67 : ℝ) / q ^ 2 = 54 / q ^ 2 + 12 / q ^ 2 + 1 / q ^ 2 := by ring
    linarith
  have hsum0 : 0 ≤ 6 * (3 / q) ^ 2 + 24 * NN * cN (2 * n) * (cN (2 * n) - c) +
      12 * NN * (cN (2 * n) - c) ^ 2 := by positivity
  have hγ : (0 : ℝ) ≤ 2 / NN := by positivity
  calc 2 / NN * √(1 + 5 / (mW n : ℝ)) * (6 * (3 / q) ^ 2 +
        24 * NN * cN (2 * n) * (cN (2 * n) - c) + 12 * NN * (cN (2 * n) - c) ^ 2)
      ≤ 2 / NN * (68 / 67) * (67 / q ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs hγ) hsum hsum0 (by positivity)
    _ = 2 / NN * (68 / q ^ 2) := by ring

/-! ## The good hidden event of the arithmetic program -/

/-- **The good hidden event of the arithmetic centre**: `goodHat n` of Part 140, and
`t|b̃ − b̂|² ≤ γ/10⁶`. It uses `(M₁, M₂)` only; no program checks it. -/
def goodA (n : ℕ) : Set (HidParam (2 * n) (mW n)) :=
  goodHat n ∩ {θ | dA n θ ≤ 2 / ((2 * n : ℕ) : ℝ) / 1000000}

lemma goodA_meas {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (goodA n) :=
  (goodHat_meas hn).inter (measurableSet_le (measurable_dA hn) measurable_const)

/-- `Pr(goodA n fails) ≤ p + 68·10⁶/(qA n)²` if `Pr(goodHat n fails) ≤ p`. -/
theorem goodA_prob_gen {n : ℕ} (hn : 4096 ≤ n) {p : ℝ}
    (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p) :
    (hidGauss (2 * n) (mW n)).real (goodA n)ᶜ ≤ p + 68000000 / (qA n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  set P := hidGauss (2 * n) (mW n) with hP
  obtain ⟨hi, hb⟩ := centreArith141 hn
  set x₀ : ℝ := 2 / ((2 * n : ℕ) : ℝ) / 1000000 with hx₀
  have hx₀0 : 0 < x₀ := by rw [hx₀]; positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := dA n)
    (Filter.Eventually.of_forall (dA_nonneg n)) hi x₀
  have h2 : P.real {θ | x₀ ≤ dA n θ} ≤ 68000000 / (qA n : ℝ) ^ 2 := by
    have h3 : x₀ * P.real {θ | x₀ ≤ dA n θ} ≤ 2 / ((2 * n : ℕ) : ℝ) * (68 / (qA n : ℝ) ^ 2) :=
      hmk.trans hb
    have e : 2 / ((2 * n : ℕ) : ℝ) * (68 / (qA n : ℝ) ^ 2) =
        x₀ * (68000000 / (qA n : ℝ) ^ 2) := by
      rw [hx₀]; field_simp; ring
    rw [e] at h3
    exact le_of_mul_le_mul_left h3 hx₀0
  have hsub : (goodA n)ᶜ ⊆ (goodHat n)ᶜ ∪ {θ | x₀ ≤ dA n θ} := by
    intro θ hθ
    by_cases hg : θ ∈ goodHat n
    · right
      by_contra hc
      exact hθ ⟨hg, (le_of_lt (not_le.mp hc) : dA n θ ≤ x₀)⟩
    · exact Or.inl hg
  calc P.real (goodA n)ᶜ ≤ P.real ((goodHat n)ᶜ ∪ {θ | x₀ ≤ dA n θ}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real (goodHat n)ᶜ + P.real {θ | x₀ ≤ dA n θ} := measureReal_union_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- `Pr(goodA n fails) ≤ 0.002 + 70/n + 68·10⁶/(qA n)²`. -/
theorem goodA_prob {n : ℕ} (hn : 4096 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodA n)ᶜ ≤
      2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  refine goodA_prob_gen hn ?_
  have := goodHat_prob hn
  rw [measureReal_compl (goodHat_meas hn1), probReal_univ]
  linarith

/-! ## The scalars on the good event -/

section good

variable {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodA n)

include hn hθ

/-- On `goodA n`, with `γ = 2/N`: `τ̂₀² ≥ 0.46·γ`, `τ̃₀² ≥ 0.458·γ` and
`(τ̃₀² − τ̂₀²)² ≤ γ²·(42·t|b̃ − b̂|²/γ + 3/(qA n)²)`. -/
theorem scalarA :
    2 / ((2 * n : ℕ) : ℝ) * (46 / 100) ≤ tauHat (2 * n) (mW n) θ ^ 2 ∧
    2 / ((2 * n : ℕ) : ℝ) * (458 / 1000) ≤ tauA n θ ^ 2 ∧
    (tauA n θ ^ 2 - tauHat (2 * n) (mW n) θ ^ 2) ^ 2 ≤
      (2 / ((2 * n : ℕ) : ℝ)) ^ 2 *
        (42 * (dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 3 * (1 / (qA n : ℝ)) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ) with hγd
  have hγ : 0 < γ := by rw [hγd, hNcast]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγd, hNcast, div_le_one (by positivity)]
    linarith
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have hqR : (40960000 : ℝ) ≤ qA n := by rw [qA_cast]; linarith
  obtain ⟨hB1, hB2⟩ := Bh_hat hn hθ.1
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  have hdle : dA n θ ≤ γ / 1000000 := hθ.2
  have hd0 := dA_nonneg n θ
  set B : ℝ := Bh (2 * n) (mW n) θ with hBd
  set B' : ℝ := 2 / (mW n : ℝ) * normSq (bA n θ) with hB'd
  set c : ℝ := c1Hat (2 * n) with hcd
  set c' : ℝ := ((c1A n : ℚ) : ℝ) with hc'd
  have hB'0 : 0 ≤ B' := mul_nonneg (by positivity) (normSq_nonneg _)
  -- the squares of the two scalars
  have eT : tauHat (2 * n) (mW n) θ ^ 2 = B * relu (B * c - 1) := by
    rw [← tauOf_bhat]
    unfold tauOf
    rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (normSq_nonneg _))
      (relu_nonneg _))]
    rfl
  have eT' : tauA n θ ^ 2 = B' * relu (B' * c' - 1) := by
    unfold tauA tauOf
    rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (normSq_nonneg _))
      (relu_nonneg _))]
  -- normalized units
  have hκ : γ * c = 1 / kap1 (2 * n) ^ 2 := by
    rw [hcd]
    unfold c1Hat
    rw [← hγd]
    field_simp
  have hksq1 : (49372 / 100000 : ℝ) ^ 2 ≤ kap1 (2 * n) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hk1 2
  have hksq2 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hk2 2
  have hkpos : (0 : ℝ) < kap1 (2 * n) ^ 2 := by nlinarith
  have hκ1 : 4101 / 1000 ≤ γ * c := by
    rw [hκ, le_div_iff₀ hkpos]
    nlinarith
  have hκ2 : γ * c ≤ 41025 / 10000 := by
    rw [hκ, div_le_iff₀ hkpos]
    nlinarith
  have hcerr : |γ * c' - γ * c| ≤ 1 / (qA n : ℝ) * (γ * c) := by
    rw [← mul_sub, abs_mul, abs_of_pos hγ]
    have h1 := c1A_err hn1
    have h2 : γ * |c' - c| ≤ 1 * (1 / (qA n : ℝ)) :=
      mul_le_mul hγ1 h1 (abs_nonneg _) (by norm_num)
    have h3 : (1 : ℝ) / (qA n : ℝ) * 1 ≤ 1 / (qA n : ℝ) * (γ * c) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hdiff : (B' - B) ^ 2 ≤ 2 * dA n θ * (B' + B) := by
    have h := normSq_diff_sq (bA n θ) (bhat θ)
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (2 / (mW n : ℝ)) ^ 2)
    have e1 : (B' - B) ^ 2 = (2 / (mW n : ℝ)) ^ 2 * (normSq (bA n θ) - normSq (bhat θ)) ^ 2 := by
      rw [hB'd, hBd]; unfold Bh; ring
    have e2 : 2 * dA n θ * (B' + B) = (2 / (mW n : ℝ)) ^ 2 *
        (2 * normSq (bA n θ - bhat θ) * (normSq (bA n θ) + normSq (bhat θ))) := by
      rw [hB'd, hBd]; unfold Bh dA; ring
    rw [e1, e2]
    exact h2
  have hN := tauN (β := B / γ) (β' := B' / γ) (κ := γ * c) (κ' := γ * c') (ξ := dA n θ / γ)
    (e := 1 / (qA n : ℝ))
    (by rw [le_div_iff₀ hγ]; linarith) (by rw [div_le_iff₀ hγ]; linarith) (by positivity)
    (by positivity) (by rw [div_le_iff₀ hγ]; linarith)
    (by
      have e1 : (B' / γ - B / γ) ^ 2 = (B' - B) ^ 2 / γ ^ 2 := by field_simp
      have e2 : 2 * (dA n θ / γ) * (B' / γ + B / γ) = 2 * dA n θ * (B' + B) / γ ^ 2 := by
        field_simp
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hdiff (by positivity))
    hκ1 hκ2 hcerr (by positivity)
    (by rw [div_le_div_iff₀ hq' (by norm_num)]; linarith)
  have eN : B / γ * (γ * c) = B * c := by field_simp
  have eN' : B' / γ * (γ * c') = B' * c' := by field_simp
  rw [eN, eN'] at hN
  obtain ⟨hN1, hN2, hN3⟩ := hN
  rw [eT, eT']
  have ea : B * relu (B * c - 1) = γ * (B / γ * relu (B * c - 1)) := by field_simp
  have eb : B' * relu (B' * c' - 1) = γ * (B' / γ * relu (B' * c' - 1)) := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [ea]; exact mul_le_mul_of_nonneg_left hN1 hγ.le
  · rw [eb]; exact mul_le_mul_of_nonneg_left hN2 hγ.le
  · rw [ea, eb, ← mul_sub, mul_pow]
    exact mul_le_mul_of_nonneg_left hN3 (by positivity)

lemma tauA_pos : 0 < tauA n θ := by
  have h := (scalarA hn hθ).2.1
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have h0 : 0 ≤ tauA n θ := by unfold tauA tauOf; exact Real.sqrt_nonneg _
  have hsq : 0 < tauA n θ ^ 2 := by nlinarith
  exact lt_of_le_of_ne h0 (fun h => by rw [← h] at hsq; norm_num at hsq)

/-- **The Hellinger price of the arithmetic centre and scalar.** On `goodA n`:
`8·hellG n τ̃₀ τ̂₀ + 2n·t|b̃ − b̂|²/τ̃₀² ≤ n·(404·t|b̃ − b̂|²/γ + 29/(qA n)²)`. -/
theorem KA_le :
    8 * hellG n (tauA n θ) (tauHat (2 * n) (mW n) θ) +
        2 * (n : ℝ) * dA n θ / tauA n θ ^ 2 ≤
      (n : ℝ) * (404 * (dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ) with hγd
  have hγ : 0 < γ := by rw [hγd, hNcast]; positivity
  obtain ⟨h1, h2, h3⟩ := scalarA hn hθ
  rw [← hγd] at h1 h2 h3
  have ha := tauA_pos hn hθ
  have hb := tauHat_pos hn hθ.1
  have hd0 := dA_nonneg n θ
  set a : ℝ := tauA n θ with had
  set b : ℝ := tauHat (2 * n) (mW n) θ with hbd
  set T' : ℝ := a ^ 2 / γ with hT'
  set T : ℝ := b ^ 2 / γ with hT
  set ξ : ℝ := dA n θ / γ with hξ
  have hTl : 46 / 100 ≤ T := by rw [hT, le_div_iff₀ hγ]; linarith
  have hT'l : 458 / 1000 ≤ T' := by rw [hT', le_div_iff₀ hγ]; linarith
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hD : (T' - T) ^ 2 ≤ 42 * ξ + 3 * (1 / (qA n : ℝ)) ^ 2 := by
    have e : (T' - T) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 / γ ^ 2 := by rw [hT', hT]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have hK := K_num hTl hT'l hξ0 hD
  have hH := hellG_le (n := n) (by omega) ha.le hb
  have hF := hell_frac ha.le hb
  have e1 : (a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 + b ^ 2) ^ 2 = (T' - T) ^ 2 / (T' + T) ^ 2 := by
    rw [hT', hT]; field_simp
  have e2 : 2 * (n : ℝ) * dA n θ / a ^ 2 = (n : ℝ) * (2 * ξ / T') := by
    rw [hT', hξ]; field_simp
  have hH2 : hellG n a b ≤ (n : ℝ) * ((T' - T) ^ 2 / (T' + T) ^ 2) := by
    rw [← e1]
    refine hH.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hF hnpos.le
  rw [e2]
  have := mul_le_mul_of_nonneg_left hK hnpos.le
  nlinarith

end good

end BstLean.Part141

open BstLean.Part141 in
#print axioms atomErrA
open BstLean.Part141 in
#print axioms centreArith141
open BstLean.Part141 in
#print axioms goodA_prob
open BstLean.Part141 in
#print axioms scalarA
open BstLean.Part141 in
#print axioms KA_le
