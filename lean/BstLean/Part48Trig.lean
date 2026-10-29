import BstLean.Part48Defs

/-!
# Part 48, wave 1: `s ↦ P(X_s)` is a trigonometric polynomial (omQ4 §4) — proved

Specification: `delegations/answers/p48-spec-opus.md`, §3 and §5.

* `trig_of_poly` (proved): `s ↦ P(X_s)` is a trigonometric polynomial of degree `≤ deg P`.
  Route used: `IsTrig` is closed under `0`, sums, scalar multiples and raising the degree;
  `cos(js)·(α cos s + β sin s)` and `sin(js)·(…)` have degree `≤ j + 1` (product-to-sum, with the
  case `j = 0` apart); induction on the exponent and on `d.support`; `MvPolynomial.eval_eq` and
  `MvPolynomial.le_totalDegree`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part48

open MeasureTheory

private lemma isTrig_zero (h : ℕ) : IsTrig h (fun _ => 0) :=
  ⟨fun _ => 0, fun _ => 0, fun s => by simp⟩

private lemma isTrig_add {h : ℕ} {F G : ℝ → ℝ} (hF : IsTrig h F) (hG : IsTrig h G) :
    IsTrig h (fun s => F s + G s) := by
  obtain ⟨a, b, hab⟩ := hF
  obtain ⟨a', b', hab'⟩ := hG
  refine ⟨fun j => a j + a' j, fun j => b j + b' j, fun s => ?_⟩
  show F s + G s = _
  rw [hab, hab', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma isTrig_smul {h : ℕ} {F : ℝ → ℝ} (c : ℝ) (hF : IsTrig h F) :
    IsTrig h (fun s => c * F s) := by
  obtain ⟨a, b, hab⟩ := hF
  refine ⟨fun j => c * a j, fun j => c * b j, fun s => ?_⟩
  show c * F s = _
  rw [hab, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma isTrig_sum {h : ℕ} {α : Type*} (S : Finset α) (F : α → ℝ → ℝ)
    (hF : ∀ i ∈ S, IsTrig h (F i)) : IsTrig h (fun s => ∑ i ∈ S, F i s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isTrig_zero h
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact isTrig_add (hF i (Finset.mem_insert_self _ _))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

private lemma isTrig_mono {h h' : ℕ} (hh : h ≤ h') {F : ℝ → ℝ} (hF : IsTrig h F) : IsTrig h' F := by
  obtain ⟨a, b, hab⟩ := hF
  refine ⟨fun j => if j ≤ h then a j else 0, fun j => if j ≤ h then b j else 0, fun s => ?_⟩
  rw [hab]
  have hsub : Finset.range (h + 1) ⊆ Finset.range (h' + 1) := Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≤ h := by simpa [Nat.lt_succ_iff] using hj
    simp [this]
  · intro j _ hj
    have : ¬ j ≤ h := by simpa [Nat.lt_succ_iff] using hj
    simp [this]

private lemma isTrig_cos {h j : ℕ} (hj : j ≤ h) : IsTrig h (fun s => Real.cos (j * s)) := by
  classical
  refine ⟨fun i => if i = j then 1 else 0, fun _ => 0, fun s => ?_⟩
  simp [ite_mul, Finset.sum_ite_eq', Nat.lt_succ_iff.mpr hj]

private lemma isTrig_sin {h j : ℕ} (hj : j ≤ h) : IsTrig h (fun s => Real.sin (j * s)) := by
  classical
  refine ⟨fun _ => 0, fun i => if i = j then 1 else 0, fun s => ?_⟩
  simp [ite_mul, Finset.sum_ite_eq', Nat.lt_succ_iff.mpr hj]

private lemma isTrig_const (h : ℕ) (c : ℝ) : IsTrig h (fun _ => c) := by
  have := isTrig_smul c (isTrig_cos (h := h) (j := 0) (Nat.zero_le _))
  simpa using this

/-- `cos(js)·cos s`, `sin(js)·cos s`, `cos(js)·sin s`, `sin(js)·sin s` have degree `≤ j + 1`. -/
private lemma isTrig_basis_lin {h j : ℕ} (hj : j ≤ h) (α β : ℝ) :
    IsTrig (h + 1) (fun s => Real.cos (j * s) * (α * Real.cos s + β * Real.sin s)) ∧
    IsTrig (h + 1) (fun s => Real.sin (j * s) * (α * Real.cos s + β * Real.sin s)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul, Real.sin_zero, zero_mul]
    refine ⟨?_, isTrig_zero _⟩
    have h1 := isTrig_cos (h := h + 1) (j := 1) (by omega)
    have h2 := isTrig_sin (h := h + 1) (j := 1) (by omega)
    simp only [Nat.cast_one, one_mul] at h1 h2
    exact isTrig_add (isTrig_smul α h1) (isTrig_smul β h2)
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have c2 := isTrig_cos (h := h + 1) (j := k + 2) (by omega)
    have c0 := isTrig_cos (h := h + 1) (j := k) (by omega)
    have s2 := isTrig_sin (h := h + 1) (j := k + 2) (by omega)
    have s0 := isTrig_sin (h := h + 1) (j := k) (by omega)
    have e1 : ∀ s : ℝ, ((k + 1 : ℕ) : ℝ) * s = (k : ℝ) * s + s := fun s => by push_cast; ring
    have e2 : ∀ s : ℝ, ((k + 2 : ℕ) : ℝ) * s = (k : ℝ) * s + s + s := fun s => by push_cast; ring
    constructor
    · -- cos((k+1)s) cos s = (cos((k+2)s) + cos(ks))/2, cos((k+1)s) sin s = (sin((k+2)s) − sin(ks))/2
      have := isTrig_add (isTrig_add (isTrig_smul (α / 2) c2) (isTrig_smul (α / 2) c0))
        (isTrig_add (isTrig_smul (β / 2) s2) (isTrig_smul (-(β / 2)) s0))
      convert this using 2 with s
      simp only [e1, e2, Real.cos_add, Real.sin_add]
      linear_combination (α / 2 * Real.cos ((k : ℝ) * s) - β / 2 * Real.sin ((k : ℝ) * s)) *
        Real.sin_sq_add_cos_sq s
    · have := isTrig_add (isTrig_add (isTrig_smul (α / 2) s2) (isTrig_smul (α / 2) s0))
        (isTrig_add (isTrig_smul (-(β / 2)) c2) (isTrig_smul (β / 2) c0))
      convert this using 2 with s
      simp only [e1, e2, Real.cos_add, Real.sin_add]
      linear_combination (α / 2 * Real.sin ((k : ℝ) * s) + β / 2 * Real.cos ((k : ℝ) * s)) *
        Real.sin_sq_add_cos_sq s

private lemma isTrig_mul_lin {h : ℕ} {F : ℝ → ℝ} (hF : IsTrig h F) (α β : ℝ) :
    IsTrig (h + 1) (fun s => F s * (Real.cos s * α + Real.sin s * β)) := by
  obtain ⟨a, b, hab⟩ := hF
  have hT : IsTrig (h + 1) (fun s => ∑ j ∈ Finset.range (h + 1),
      (a j * (Real.cos (j * s) * (α * Real.cos s + β * Real.sin s)) +
        b j * (Real.sin (j * s) * (α * Real.cos s + β * Real.sin s)))) := by
    refine isTrig_sum _ _ fun j hj => ?_
    have hjh : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact isTrig_add (isTrig_smul (a j) (isTrig_basis_lin hjh α β).1)
      (isTrig_smul (b j) (isTrig_basis_lin hjh α β).2)
  convert hT using 2 with s
  rw [hab, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma isTrig_mul_linpow {h : ℕ} {F : ℝ → ℝ} (hF : IsTrig h F) (α β : ℝ) (m : ℕ) :
    IsTrig (h + m) (fun s => F s * (Real.cos s * α + Real.sin s * β) ^ m) := by
  induction m with
  | zero => simpa using hF
  | succ m ih =>
    have := isTrig_mul_lin ih α β
    convert this using 2 with s
    ring

private lemma isTrig_prod {ι : Type*} (S : Finset ι) (e : ι → ℕ) (x y : ι → ℝ) :
    IsTrig (∑ i ∈ S, e i) (fun s => ∏ i ∈ S, (Real.cos s * x i + Real.sin s * y i) ^ e i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isTrig_const 0 1
  | insert i S hi ih =>
    have := isTrig_mul_linpow ih (x i) (y i) (e i)
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    convert this using 1
    · ring
    · funext s; ring

/-- `s ↦ P(X_s)` is a trigonometric polynomial of degree `≤ h` when `deg P ≤ h`. -/
theorem trig_of_poly {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℝ) (h : ℕ) (hP : P.totalDegree ≤ h)
    (x y : ι → ℝ) : IsTrig h (fun s => MvPolynomial.eval (rotX s x y) P) := by
  have hT : IsTrig h (fun s => ∑ d ∈ P.support,
      P.coeff d * ∏ i ∈ d.support, (Real.cos s * x i + Real.sin s * y i) ^ d i) := by
    refine isTrig_sum _ _ fun d hd => isTrig_smul _ (isTrig_mono ?_ (isTrig_prod d.support d x y))
    exact (MvPolynomial.le_totalDegree hd).trans hP
  convert hT using 2 with s
  rw [MvPolynomial.eval_eq]
  rfl


end BstLean.Part48
