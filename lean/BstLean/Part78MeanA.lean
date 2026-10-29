import BstLean.Part78Defs

/-!
# Part 78: generic tools for `regIface` and `meanIds`

* `Good`: a function on `ι → ℝ` with every finite moment under `stdGauss`.
* separable sums `Σ_k c_k(W) ψ_k(x)` and the exchange of integrals for them.
-/

namespace BstLean.Part78

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)

/-! ## Functions with all moments -/

/-- All finite moments under `μ`. -/
def Good {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ p : ℝ≥0, MemLp f p μ

section good
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma Good.integrable {f : Ω → ℝ} (hf : Good μ f) : Integrable f μ :=
  memLp_one_iff_integrable.1 (by simpa using hf 1)

lemma Good.add {f g : Ω → ℝ} (hf : Good μ f) (hg : Good μ g) : Good μ (fun w => f w + g w) :=
  fun p => (hf p).add (hg p)

lemma Good.sub {f g : Ω → ℝ} (hf : Good μ f) (hg : Good μ g) : Good μ (fun w => f w - g w) :=
  fun p => (hf p).sub (hg p)

lemma Good.const_mul {f : Ω → ℝ} (hf : Good μ f) (c : ℝ) : Good μ (fun w => c * f w) :=
  fun p => (hf p).const_mul c

lemma Good.mul_const {f : Ω → ℝ} (hf : Good μ f) (c : ℝ) : Good μ (fun w => f w * c) := by
  simpa [mul_comm] using hf.const_mul c

lemma Good.mul {f g : Ω → ℝ} (hf : Good μ f) (hg : Good μ g) : Good μ (fun w => f w * g w) := by
  intro p
  have h1 := hf (2 * p)
  have h2 := hg (2 * p)
  have : ENNReal.HolderTriple ((2 * p : ℝ≥0) : ℝ≥0∞) ((2 * p : ℝ≥0) : ℝ≥0∞) (p : ℝ≥0∞) := by
    constructor
    rw [ENNReal.coe_mul, ENNReal.coe_ofNat]
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact (h1.mul h2 : MemLp (f * g) (p : ℝ≥0∞) μ)

lemma Good.pow {f : Ω → ℝ} (hf : Good μ f) [IsFiniteMeasure μ] (k : ℕ) :
    Good μ (fun w => f w ^ k) := by
  induction k with
  | zero => intro p; simpa using memLp_const (1 : ℝ)
  | succ k ih => simpa [pow_succ] using ih.mul hf

lemma Good.const [IsFiniteMeasure μ] (c : ℝ) : Good μ (fun _ : Ω => c) := fun _ => memLp_const c

lemma Good.sum {K : Type*} (s : Finset K) {f : K → Ω → ℝ} (hf : ∀ k ∈ s, Good μ (f k)) :
    Good μ (fun w => ∑ k ∈ s, f k w) :=
  fun p => memLp_finsetSum s (fun k hk => hf k hk p)

end good

lemma good_coord {ι : Type*} [Fintype ι] (β : ι) : Good (stdGauss ι) (fun W : ι → ℝ => W β) := by
  intro p
  have h : MemLp (id : ℝ → ℝ) p (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.memLp_id_gaussianReal p
  have hmp : MeasurePreserving (Function.eval β) (stdGauss ι) (ProbabilityTheory.gaussianReal 0 1) := by
    unfold stdGauss
    exact measurePreserving_eval (fun _ : ι => ProbabilityTheory.gaussianReal 0 1) β
  exact h.comp_measurePreserving hmp

/-! ## Separable sums -/

section sep
variable {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype K]
  {μ : Measure Ω} {ν : Measure X} (c : K → Ω → ℝ) (ψ : K → X → ℝ)

lemma sep_int (hψ : ∀ k, Integrable (ψ k) ν) (W : Ω) :
    ∫ x, ∑ k, c k W * ψ k x ∂ν = ∑ k, c k W * ∫ x, ψ k x ∂ν := by
  rw [integral_finsetSum _ (fun k _ => (hψ k).const_mul _)]
  simp_rw [integral_const_mul]

lemma sep_mul (c' : K → Ω → ℝ) (ψ' : K → X → ℝ) (W W' : Ω) (x y : X) :
    (∑ k, c k W * ψ k x) * (∑ l, c' l W' * ψ' l y) =
      ∑ kl : K × K, (c kl.1 W * c' kl.2 W') * (ψ kl.1 x * ψ' kl.2 y) := by
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma sep_int_sq (hψ2 : ∀ k l, Integrable (fun x => ψ k x * ψ l x) ν) (W : Ω) :
    ∫ x, (∑ k, c k W * ψ k x) ^ 2 ∂ν =
      ∑ kl : K × K, (c kl.1 W * c kl.2 W) * ∫ x, ψ kl.1 x * ψ kl.2 x ∂ν := by
  simp_rw [sq, sep_mul c ψ c ψ]
  exact sep_int (fun (kl : K × K) (W : Ω) => c kl.1 W * c kl.2 W)
    (fun (kl : K × K) x => ψ kl.1 x * ψ kl.2 x) (fun kl => hψ2 kl.1 kl.2) W

lemma sep_swap (hc : ∀ k, Integrable (c k) μ) (hψ : ∀ k, Integrable (ψ k) ν) :
    ∫ W, ∫ x, ∑ k, c k W * ψ k x ∂ν ∂μ = ∫ x, ∫ W, ∑ k, c k W * ψ k x ∂μ ∂ν := by
  simp_rw [sep_int c ψ hψ]
  rw [integral_finsetSum _ (fun k _ => (hc k).mul_const _)]
  have h : ∀ x, ∫ W, ∑ k, c k W * ψ k x ∂μ = ∑ k, (∫ W, c k W ∂μ) * ψ k x := by
    intro x
    rw [integral_finsetSum _ (fun k _ => (hc k).mul_const _)]
    simp_rw [integral_mul_const]
  simp_rw [h]
  rw [integral_finsetSum _ (fun k _ => (hψ k).const_mul _)]
  simp_rw [integral_mul_const, integral_const_mul]

lemma sep_swap_sq (hc2 : ∀ k l, Integrable (fun W => c k W * c l W) μ)
    (hψ2 : ∀ k l, Integrable (fun x => ψ k x * ψ l x) ν) :
    ∫ W, ∫ x, (∑ k, c k W * ψ k x) ^ 2 ∂ν ∂μ = ∫ x, ∫ W, (∑ k, c k W * ψ k x) ^ 2 ∂μ ∂ν := by
  simp_rw [sq, sep_mul c ψ c ψ]
  exact sep_swap (fun (kl : K × K) (W : Ω) => c kl.1 W * c kl.2 W)
    (fun (kl : K × K) x => ψ kl.1 x * ψ kl.2 x) (fun kl => hc2 kl.1 kl.2) (fun kl => hψ2 kl.1 kl.2)

lemma sep_swap_two (hc2 : ∀ k l, Integrable (fun W => c k W * c l W) μ)
    (hψ : ∀ k, Integrable (ψ k) ν) :
    ∫ W, (∫ x, ∑ k, c k W * ψ k x ∂ν) ^ 2 ∂μ =
      ∫ x, ∫ y, ∫ W, (∑ k, c k W * ψ k x) * (∑ k, c k W * ψ k y) ∂μ ∂ν ∂ν := by
  have h : ∀ x y, ∫ W, (∑ k, c k W * ψ k x) * (∑ k, c k W * ψ k y) ∂μ =
      ∑ kl : K × K, (∫ W, c kl.1 W * c kl.2 W ∂μ) * (ψ kl.1 x * ψ kl.2 y) := by
    intro x y
    simp_rw [sep_mul c ψ c ψ]
    rw [integral_finsetSum _ (fun kl _ => (hc2 kl.1 kl.2).mul_const _)]
    simp_rw [integral_mul_const]
  simp_rw [h, sep_int c ψ hψ, sq]
  have h2 : ∀ W, (∑ k, c k W * ∫ x, ψ k x ∂ν) * (∑ k, c k W * ∫ x, ψ k x ∂ν) =
      ∑ kl : K × K, (c kl.1 W * c kl.2 W) * ((∫ x, ψ kl.1 x ∂ν) * ∫ x, ψ kl.2 x ∂ν) := by
    intro W
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [h2]
  rw [integral_finsetSum _ (fun kl _ => (hc2 kl.1 kl.2).mul_const _)]
  have h3 : ∀ x, ∫ y, ∑ kl : K × K, (∫ W, c kl.1 W * c kl.2 W ∂μ) * (ψ kl.1 x * ψ kl.2 y) ∂ν =
      ∑ kl : K × K, ((∫ W, c kl.1 W * c kl.2 W ∂μ) * ∫ y, ψ kl.2 y ∂ν) * ψ kl.1 x := by
    intro x
    rw [integral_finsetSum _ (fun kl _ => ((hψ kl.2).const_mul _).const_mul _)]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [integral_const_mul, integral_const_mul]; ring
  simp_rw [h3]
  rw [integral_finsetSum _ (fun kl _ => (hψ kl.1).const_mul _)]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [integral_const_mul, integral_mul_const]; ring

end sep

end BstLean.Part78
