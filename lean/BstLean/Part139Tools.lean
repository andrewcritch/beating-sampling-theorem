import BstLean.Part133All

/-!
# Part 139, tools

* `covV_trace`, `covV_frob_le` (T3): the trace and a Frobenius bound of the covariance of a
  bounded vector function, in terms of the kernel `K(ω, ω′) = Σ_i z_i(ω) z_i(ω′)`.
* `qform_sq_integral` (T1): `E (hᵀCh)² = (tr C)² + 2 Σ_ij C_ij²` for a standard Gaussian vector
  `h` and a symmetric matrix `C`.
* `kappa6_zero_le`, `kappa6_zero_le'` (T2): `κ^[6] 0 ≤ 7775/10000 ≤ 778/1000`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part29 (stdGauss)

/-! ## Bounded measurable functions -/

/-- Measurable and bounded. -/
def BM {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop :=
  Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B

namespace BM

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma const (c : ℝ) : BM (fun _ : α => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

lemma add {f g : α → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨mf, A, hA⟩ := hf
  obtain ⟨mg, B, hB⟩ := hg
  exact ⟨mf.add mg, A + B, fun x => (abs_add_le _ _).trans (add_le_add (hA x) (hB x))⟩

lemma sub {f g : α → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x - g x) := by
  obtain ⟨mf, A, hA⟩ := hf
  obtain ⟨mg, B, hB⟩ := hg
  exact ⟨mf.sub mg, A + B, fun x => (abs_sub _ _).trans (add_le_add (hA x) (hB x))⟩

lemma mul {f g : α → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨mf, A, hA⟩ := hf
  obtain ⟨mg, B, hB⟩ := hg
  refine ⟨mf.mul mg, A * B, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hA x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (hA x))

lemma sq {f : α → ℝ} (hf : BM f) : BM (fun x => f x ^ 2) := by
  simpa [pow_two] using hf.mul hf

lemma sum {κ : Type*} (s : Finset κ) {f : κ → α → ℝ} (hf : ∀ i ∈ s, BM (f i)) :
    BM (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BM.const (α := α) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma fst {f : α → ℝ} (hf : BM f) : BM (fun p : α × β => f p.1) :=
  ⟨hf.1.comp measurable_fst, hf.2.imp fun _ h p => h p.1⟩

lemma snd {f : β → ℝ} (hf : BM f) : BM (fun p : α × β => f p.2) :=
  ⟨hf.1.comp measurable_snd, hf.2.imp fun _ h p => h p.2⟩

lemma integrable {f : α → ℝ} (hf : BM f) (ν : Measure α) [IsFiniteMeasure ν] :
    Integrable f ν := by
  obtain ⟨mf, B, hB⟩ := hf
  exact Integrable.of_bound mf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

end BM

/-! ## T3: the covariance of a bounded vector function -/

section cov
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ι : Type} [Fintype ι] (z : Ω → ι → ℝ)

/-- mean vector -/
noncomputable def meanV (i : ι) : ℝ := ∫ ω, z ω i ∂μ
/-- covariance -/
noncomputable def covV (i j : ι) : ℝ := ∫ ω, (z ω i - meanV μ z i) * (z ω j - meanV μ z j) ∂μ

theorem covV_trace (hz : ∀ i, Measurable fun ω => z ω i) (hb : ∃ B : ℝ, ∀ ω i, |z ω i| ≤ B) :
    ∑ i, covV μ z i i =
      ∫ ω, ∑ i, z ω i ^ 2 ∂μ - ∫ p : Ω × Ω, ∑ i, z p.1 i * z p.2 i ∂(μ.prod μ) := by
  have hzB : ∀ i, BM (fun ω => z ω i) := fun i =>
    ⟨hz i, hb.imp fun _ hB ω => hB ω i⟩
  have h1 : ∀ i, covV μ z i i = ∫ ω, z ω i ^ 2 ∂μ - meanV μ z i * meanV μ z i := by
    intro i
    have e : (fun ω => (z ω i - meanV μ z i) * (z ω i - meanV μ z i)) =
        fun ω => z ω i ^ 2 - 2 * meanV μ z i * z ω i + meanV μ z i * meanV μ z i := by
      funext ω; ring
    have i1 : Integrable (fun ω => z ω i ^ 2) μ := (hzB i).sq.integrable μ
    have i2 : Integrable (fun ω => 2 * meanV μ z i * z ω i) μ :=
      ((hzB i).integrable μ).const_mul _
    have i3 : Integrable (fun ω => z ω i ^ 2 - 2 * meanV μ z i * z ω i) μ := i1.sub i2
    unfold covV
    rw [e, integral_add i3 (integrable_const _), integral_sub i1 i2, integral_const_mul,
      integral_const]
    simp only [probReal_univ, one_smul]
    unfold meanV
    ring
  have h2 : ∫ ω, ∑ i, z ω i ^ 2 ∂μ = ∑ i, ∫ ω, z ω i ^ 2 ∂μ :=
    integral_finsetSum _ fun i _ => (hzB i).sq.integrable μ
  have h3 : ∫ p : Ω × Ω, ∑ i, z p.1 i * z p.2 i ∂(μ.prod μ) =
      ∑ i, meanV μ z i * meanV μ z i := by
    rw [integral_finsetSum _ fun i _ => ((hzB i).fst.mul (hzB i).snd).integrable (μ.prod μ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_prod_mul (fun ω => z ω i) (fun ω => z ω i)
  rw [h2, h3, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => h1 i

theorem covV_frob_le (hz : ∀ i, Measurable fun ω => z ω i) (hb : ∃ B : ℝ, ∀ ω i, |z ω i| ≤ B)
    (c : ℝ) :
    ∑ i, ∑ j, covV μ z i j ^ 2 ≤
      ∫ p : Ω × Ω, (∑ i, z p.1 i * z p.2 i - c) ^ 2 ∂(μ.prod μ) := by
  have hzB : ∀ i, BM (fun ω => z ω i) := fun i =>
    ⟨hz i, hb.imp fun _ hB ω => hB ω i⟩
  let a : ι → ℝ := meanV μ z
  let ζ : Ω → ι → ℝ := fun ω i => z ω i - a i
  have hζB : ∀ i, BM (fun ω => ζ ω i) := fun i => (hzB i).sub (BM.const _)
  have hζ0 : ∀ i, ∫ ω, ζ ω i ∂μ = 0 := by
    intro i
    simp only [ζ]
    rw [integral_sub ((hzB i).integrable μ) (integrable_const _), integral_const]
    simp [a, meanV]
  let r : Ω → ℝ := fun ω => ∑ i, ζ ω i * a i
  have hrB : BM r := BM.sum _ fun i _ => (hζB i).mul (BM.const _)
  let c0 : ℝ := ∑ i, a i * a i - c
  let P : Ω × Ω → ℝ := fun p => ∑ i, ζ p.1 i * ζ p.2 i
  let R : Ω × Ω → ℝ := fun p => r p.1 + r p.2 + c0
  have hK : ∀ p : Ω × Ω, ∑ i, z p.1 i * z p.2 i - c = P p + R p := by
    intro p
    have e : ∑ i, z p.1 i * z p.2 i =
        ∑ i, ζ p.1 i * ζ p.2 i + ∑ i, ζ p.1 i * a i + ∑ i, ζ p.2 i * a i + ∑ i, a i * a i := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [ζ]; ring
    simp only [P, R, r, c0]
    linarith
  have hPB : BM P := BM.sum _ fun i _ => (hζB i).fst.mul (hζB i).snd
  have hRB : BM R := (hrB.fst.add hrB.snd).add (BM.const _)
  have hPR : ∫ p, P p * R p ∂(μ.prod μ) = 0 := by
    have e : (fun p => P p * R p) = fun p : Ω × Ω =>
        ∑ i, ((ζ p.1 i * (r p.1 + c0)) * ζ p.2 i + ζ p.1 i * (ζ p.2 i * r p.2)) := by
      funext p
      simp only [P, R]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hi1 : ∀ i, Integrable (fun p : Ω × Ω => (ζ p.1 i * (r p.1 + c0)) * ζ p.2 i)
        (μ.prod μ) := fun i =>
      (((hζB i).mul (hrB.add (BM.const c0))).fst.mul (hζB i).snd).integrable _
    have hi2 : ∀ i, Integrable (fun p : Ω × Ω => ζ p.1 i * (ζ p.2 i * r p.2))
        (μ.prod μ) := fun i =>
      ((hζB i).fst.mul ((hζB i).mul hrB).snd).integrable _
    have hi12 : ∀ i, Integrable (fun p : Ω × Ω =>
        (ζ p.1 i * (r p.1 + c0)) * ζ p.2 i + ζ p.1 i * (ζ p.2 i * r p.2)) (μ.prod μ) :=
      fun i => (hi1 i).add (hi2 i)
    rw [e, integral_finsetSum _ fun i _ => hi12 i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_add (hi1 i) (hi2 i),
      integral_prod_mul (fun ω => ζ ω i * (r ω + c0)) (fun ω => ζ ω i),
      integral_prod_mul (fun ω => ζ ω i) (fun ω => ζ ω i * r ω), hζ0 i]
    simp
  have hPP : ∫ p, P p ^ 2 ∂(μ.prod μ) = ∑ i, ∑ j, covV μ z i j ^ 2 := by
    have e : (fun p => P p ^ 2) = fun p : Ω × Ω =>
        ∑ i, ∑ j, (ζ p.1 i * ζ p.1 j) * (ζ p.2 i * ζ p.2 j) := by
      funext p
      simp only [P]
      rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hi : ∀ i j, Integrable (fun p : Ω × Ω => (ζ p.1 i * ζ p.1 j) * (ζ p.2 i * ζ p.2 j))
        (μ.prod μ) := fun i j =>
      (((hζB i).mul (hζB j)).fst.mul ((hζB i).mul (hζB j)).snd).integrable _
    rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_prod_mul (fun ω => ζ ω i * ζ ω j) (fun ω => ζ ω i * ζ ω j), pow_two]
    rfl
  rw [← hPP]
  have e2 : ∫ p, P p ^ 2 ∂(μ.prod μ) = ∫ p, (P p ^ 2 + 2 * (P p * R p)) ∂(μ.prod μ) := by
    rw [integral_add (hPB.sq.integrable _) (((hPB.mul hRB).integrable _).const_mul 2),
      integral_const_mul, hPR]
    simp
  rw [e2]
  refine integral_mono ((hPB.sq.integrable _).add (((hPB.mul hRB).integrable _).const_mul 2))
    ?_ fun p => ?_
  · have hKB : BM (fun p : Ω × Ω => (P p + R p) ^ 2) := (hPB.add hRB).sq
    have e3 : (fun p : Ω × Ω => (∑ i, z p.1 i * z p.2 i - c) ^ 2) =
        fun p => (P p + R p) ^ 2 := by
      funext p; rw [hK p]
    rw [e3]
    exact hKB.integrable _
  · simp only
    rw [hK p]
    nlinarith [sq_nonneg (R p)]

end cov

/-! ## T1: the second moment of a Gaussian quadratic form -/

section qform

open BstLean.Part29 (gaussMom gaussMom_eq)
open BstLean.Part130 (integrable_pow_gauss)
open BstLean.Part131 (qform_expand)

variable {ι : Type} [Fintype ι]

lemma abs_mul4_le (a b c d : ℝ) : |a * b * c * d| ≤ a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 := by
  rw [abs_le]
  constructor <;>
  nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * b + c * d), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (c ^ 2 - d ^ 2), sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (c ^ 2),
    sq_nonneg (d ^ 2)]

lemma four_integrable (i j k l : ι) :
    Integrable (fun h : ι → ℝ => h i * h j * h k * h l) (stdGauss ι) := by
  unfold stdGauss
  have h4 : ∀ m : ι, Integrable (fun h : ι → ℝ => h m ^ 4)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := fun m =>
    integrable_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := m) (integrable_pow_gauss 4)
  have hs : Integrable (fun h : ι → ℝ => h i ^ 4 + h j ^ 4 + h k ^ 4 + h l ^ 4)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := (((h4 i).add (h4 j)).add (h4 k)).add (h4 l)
  refine Integrable.mono' hs ?_ (Filter.Eventually.of_forall fun h => ?_)
  · exact ((((measurable_pi_apply i).mul (measurable_pi_apply j)).mul
      (measurable_pi_apply k)).mul (measurable_pi_apply l)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_mul4_le _ _ _ _

lemma gaussMom_small : gaussMom 0 = 1 ∧ gaussMom 1 = 0 ∧ gaussMom 2 = 1 ∧ gaussMom 3 = 0 ∧
    gaussMom 4 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold gaussMom
    split_ifs with h
    · first
        | exact absurd h (by decide)
        | norm_num [Nat.doubleFactorial]
    · first
        | rfl
        | exact absurd (by decide) h

/-- The fourth moments of a standard Gaussian vector (Wick, Isserlis). -/
lemma four_moment [DecidableEq ι] (i j k l : ι) :
    ∫ h, h i * h j * h k * h l ∂stdGauss ι =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
      (if i = k then 1 else 0) * (if j = l then 1 else 0) +
      (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  obtain ⟨g0, g1, g2, g3, g4⟩ := gaussMom_small
  let e : ι → ℕ := fun m => (if i = m then 1 else 0) + (if j = m then 1 else 0) +
    (if k = m then 1 else 0) + (if l = m then 1 else 0)
  have hprod : ∀ h : ι → ℝ, h i * h j * h k * h l = ∏ m, h m ^ e m := by
    intro h
    simp only [e, pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole]
    simp
  have key : ∫ h : ι → ℝ, ∏ m, h m ^ e m ∂stdGauss ι = ∏ m, gaussMom (e m) := by
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (f := fun m (x : ℝ) => x ^ e m)]
    simp_rw [gaussMom_eq]
  simp_rw [hprod]
  rw [key]
  have hz : ∀ a : ι, e a = 1 → ∏ m, gaussMom (e m) = 0 := fun a ha =>
    Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha, g1])
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        rw [Finset.prod_eq_single i]
        · simp [e, g4]; norm_num
        · intro m _ hm
          simp [e, Ne.symm hm, g0]
        · simp
      · have : ∀ m, gaussMom (e m) = 1 := by
          intro m
          by_cases h1 : i = m
          · subst h1
            simp [e, Ne.symm hik, g2]
          · by_cases h2 : k = m
            · subst h2
              simp [e, h1, g2]
            · simp [e, h1, h2, g0]
        rw [Finset.prod_eq_one fun m _ => this m]
        simp [hik]
    · by_cases hik : i = k
      · subst hik
        rw [hz l (by simp [e, hkl])]
        simp [hkl]
      · rw [hz k (by simp [e, hik, Ne.symm hkl])]
        simp [hkl, hik]
  · by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        rw [hz j (by simp [e, hij])]
        simp [hij, Ne.symm hij]
      · rw [hz i (by simp [e, Ne.symm hij, Ne.symm hik])]
        simp [hij, hik]
    · by_cases hik : i = k
      · subst hik
        by_cases hjl : j = l
        · subst hjl
          have : ∀ m, gaussMom (e m) = 1 := by
            intro m
            by_cases h1 : i = m
            · subst h1
              simp [e, Ne.symm hij, g2]
            · by_cases h2 : j = m
              · subst h2
                simp [e, h1, g2]
              · simp [e, h1, h2, g0]
          rw [Finset.prod_eq_one fun m _ => this m]
          simp [hij, Ne.symm hij]
        · rw [hz j (by simp [e, hij, Ne.symm hjl])]
          simp [hij, hjl, hkl]
      · by_cases hil : i = l
        · subst hil
          by_cases hjk : j = k
          · subst hjk
            have : ∀ m, gaussMom (e m) = 1 := by
              intro m
              by_cases h1 : i = m
              · subst h1
                simp [e, Ne.symm hij, g2]
              · by_cases h2 : j = m
                · subst h2
                  simp [e, h1, g2]
                · simp [e, h1, h2, g0]
            rw [Finset.prod_eq_one fun m _ => this m]
            simp [hij, Ne.symm hij]
          · rw [hz j (by simp [e, hij, Ne.symm hjk])]
            simp [hij, hjk, hik]
        · rw [hz i (by simp [e, Ne.symm hij, Ne.symm hik, Ne.symm hil])]
          simp [hij, hik, hil]

theorem qform_sq_integral (C : Matrix ι ι ℝ) (hC : C.transpose = C) :
    Integrable (fun h : ι → ℝ => (h ⬝ᵥ C *ᵥ h) ^ 2) (stdGauss ι) ∧
    ∫ h, (h ⬝ᵥ C *ᵥ h) ^ 2 ∂stdGauss ι = C.trace ^ 2 + 2 * ∑ i, ∑ j, C i j ^ 2 := by
  classical
  have hexp : (fun h : ι → ℝ => (h ⬝ᵥ C *ᵥ h) ^ 2) = fun h =>
      ∑ i, ∑ j, ∑ k, ∑ l, C i j * C k l * (h i * h j * h k * h l) := by
    funext h
    rw [qform_expand, pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hi : ∀ i j k l, Integrable
      (fun h : ι → ℝ => C i j * C k l * (h i * h j * h k * h l)) (stdGauss ι) :=
    fun i j k l => (four_integrable i j k l).const_mul _
  have hi3 : ∀ i j k, Integrable
      (fun h : ι → ℝ => ∑ l, C i j * C k l * (h i * h j * h k * h l)) (stdGauss ι) :=
    fun i j k => integrable_finsetSum _ fun l _ => hi i j k l
  have hi2 : ∀ i j, Integrable
      (fun h : ι → ℝ => ∑ k, ∑ l, C i j * C k l * (h i * h j * h k * h l)) (stdGauss ι) :=
    fun i j => integrable_finsetSum _ fun k _ => hi3 i j k
  have hi1 : ∀ i, Integrable
      (fun h : ι → ℝ => ∑ j, ∑ k, ∑ l, C i j * C k l * (h i * h j * h k * h l)) (stdGauss ι) :=
    fun i => integrable_finsetSum _ fun j _ => hi2 i j
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun i _ => hi1 i, ?_⟩
  have hsym : ∀ i j, C j i = C i j := fun i j => by
    have := congrFun (congrFun hC i) j
    rwa [Matrix.transpose_apply] at this
  have hint : ∫ h : ι → ℝ, ∑ i, ∑ j, ∑ k, ∑ l, C i j * C k l * (h i * h j * h k * h l)
      ∂stdGauss ι = ∑ i, ∑ j, ∑ k, ∑ l, C i j * C k l *
        ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0)) := by
    rw [integral_finsetSum _ fun i _ => hi1 i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hi2 i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hi3 i j k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => hi i j k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, four_moment]
  rw [hint]
  have s1 : ∑ i, ∑ j, ∑ k, ∑ l, C i j * C k l *
      ((if i = j then 1 else 0) * (if k = l then 1 else 0)) = C.trace ^ 2 := by
    simp [Matrix.trace, pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have s2 : ∑ i, ∑ j, ∑ k, ∑ l, C i j * C k l *
      ((if i = k then 1 else 0) * (if j = l then 1 else 0)) = ∑ i, ∑ j, C i j ^ 2 := by
    simp [pow_two]
  have s3 : ∑ i, ∑ j, ∑ k, ∑ l, C i j * C k l *
      ((if i = l then 1 else 0) * (if j = k then 1 else 0)) = ∑ i, ∑ j, C i j ^ 2 := by
    simp [pow_two, hsym]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [s1, s2, s3]
  ring

end qform

/-! ## T2: an upper bound of the sixth iterate of `κ` at `0` -/

section kappa

open BstLean.Part130 BstLean.Part132

lemma le_of_deriv_le {f g f' g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (h0 : f 0 ≤ g 0) (h : ∀ x, 0 ≤ x → f' x ≤ g' x)
    {x : ℝ} (hx : 0 ≤ x) : f x ≤ g x := by
  have hmono : MonotoneOn (fun y => g y - f y) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.2 fun y => ((hg y).sub (hf y)).continuousAt).continuousOn
    · intro y _
      exact ((hg y).sub (hf y)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hd : deriv (fun y => g y - f y) y = g' y - f' y := ((hg y).sub (hf y)).deriv
      rw [hd]
      linarith [h y (le_of_lt hy)]
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  simp only at this
  linarith

lemma sin_ge3 {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  refine le_of_deriv_le (f := fun x => x - x ^ 3 / 6) (f' := fun x => 1 - x ^ 2 / 2)
    (g := Real.sin) (g' := Real.cos) (fun y => ?_) Real.hasDerivAt_sin (by simp)
    (fun y _ => Real.one_sub_sq_div_two_le_cos) hx
  exact ((hasDerivAt_id' y).sub ((hasDerivAt_pow 3 y).div_const 6)).congr_deriv
    (by norm_num; ring)

lemma cos_le4 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  refine le_of_deriv_le (f := Real.cos) (f' := fun x => -Real.sin x)
    (g := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24) (g' := fun x => -x + x ^ 3 / 6)
    Real.hasDerivAt_cos (fun y => ?_) (by simp)
    (fun y hy => by linarith [sin_ge3 hy]) hx
  exact (((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
    ((hasDerivAt_pow 4 y).div_const 24)).congr_deriv (by norm_num; ring)

lemma sin_le5 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  refine le_of_deriv_le (f := Real.sin) (f' := Real.cos)
    (g := fun x => x - x ^ 3 / 6 + x ^ 5 / 120) (g' := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24)
    Real.hasDerivAt_sin (fun y => ?_) (by simp)
    (fun y hy => cos_le4 hy) hx
  exact (((hasDerivAt_id' y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
    ((hasDerivAt_pow 5 y).div_const 120)).congr_deriv (by norm_num; ring)

lemma cos_ge6 {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  refine le_of_deriv_le (g := Real.cos) (g' := fun x => -Real.sin x)
    (f := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)
    (f' := fun x => -x + x ^ 3 / 6 - x ^ 5 / 120)
    (fun y => ?_) Real.hasDerivAt_cos (by simp)
    (fun y hy => by linarith [sin_le5 hy]) hx
  exact ((((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
    ((hasDerivAt_pow 4 y).div_const 24)).sub
    ((hasDerivAt_pow 6 y).div_const 720)).congr_deriv (by norm_num; ring)

/-- `x − x³/6 + x⁵/120 − x⁷/5040 ≤ sin x` for `x ≥ 0`. -/
lemma sin_ge7 {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  refine le_of_deriv_le (g := Real.sin) (g' := Real.cos)
    (f := fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)
    (f' := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)
    (fun y => ?_) Real.hasDerivAt_sin (by simp)
    (fun y hy => cos_ge6 hy) hx
  exact ((((hasDerivAt_id' y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
    ((hasDerivAt_pow 5 y).div_const 120)).sub
    ((hasDerivAt_pow 7 y).div_const 5040)).congr_deriv (by norm_num; ring)

/-- One step of a rational upper bound of `κ`, valid on all of `[0, 1]`: `r` bounds
`√(1 − a²)` and `c` bounds `arcsin a` (through the lower bound `sin_ge7` of `sin c`). -/
theorem kappa_le_step {s a r c b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (ha : a ≤ 1)
    (hr0 : 0 ≤ r) (hr : 1 - a ^ 2 ≤ r ^ 2) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : a ≤ c - c ^ 3 / 6 + c ^ 5 / 120 - c ^ 7 / 5040)
    (hb : (r + a * c) / 3.141592 + a / 2 ≤ b) : kappa s ≤ b := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have ha0 : 0 ≤ a := hs.trans hsa
  have h1 := kappa_monotoneOn (a := s) (b := a) ⟨by linarith, hsa.trans ha⟩
    ⟨by linarith, ha⟩ hsa
  have hsq : Real.sqrt (1 - a ^ 2) ≤ r := by
    calc Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hr
      _ = r := Real.sqrt_sq hr0
  have hasin : Real.arcsin a ≤ c :=
    (Real.arcsin_le_iff_le_sin ⟨by linarith, ha⟩ ⟨by linarith, by linarith⟩).2
      (hc.trans (sin_ge7 hc0))
  have e : kappa a = (Real.sqrt (1 - a ^ 2) + a * Real.arcsin a) * (1 / Real.pi) + a / 2 := by
    have := kappa_deriv_eq a
    unfold kappa
    have e' : (Real.sqrt (1 - a ^ 2) + a * (Real.pi - Real.arccos a)) / Real.pi =
        Real.sqrt (1 - a ^ 2) / Real.pi + a * ((Real.pi - Real.arccos a) / Real.pi) := by ring
    rw [e', this]
    ring
  have h2 : Real.sqrt (1 - a ^ 2) + a * Real.arcsin a ≤ r + a * c :=
    add_le_add hsq (mul_le_mul_of_nonneg_left hasin ha0)
  have hrc : 0 ≤ r + a * c := by positivity
  have h3 : (Real.sqrt (1 - a ^ 2) + a * Real.arcsin a) * (1 / Real.pi) ≤
      (r + a * c) * (1 / 3.141592) :=
    mul_le_mul h2 one_div_pi_lt.le (by positivity) hrc
  have e2 : (r + a * c) * (1 / 3.141592) = (r + a * c) / 3.141592 := by ring
  linarith

theorem kappa3_zero_le : kappa (kappa (kappa 0)) ≤ 604847 / 1000000 :=
  kappa_le_step (a := 49376 / 100000) (r := 1087 / 1250) (c := 516411 / 1000000)
    (by linarith [kappa2_zero_ge]) kappa2_zero_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem kappa4_zero_le : kappa (kappa (kappa (kappa 0))) ≤ 680971 / 1000000 :=
  kappa_le_step (a := 604847 / 1000000) (r := 796343 / 1000000) (c := 81197 / 125000)
    (by linarith [kappa3_zero_ge]) kappa3_zero_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem kappa5_zero_le : kappa (kappa (kappa (kappa (kappa 0)))) ≤ 367981 / 500000 :=
  kappa_le_step (a := 680971 / 1000000) (r := 91539 / 125000) (c := 74909 / 100000)
    (by linarith [kappa4_zero_ge]) kappa4_zero_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- `κ^[6] 0 ≤ 0.777243`. -/
theorem kappa6_zero_le'' : kappa^[6] 0 ≤ 777243 / 1000000 := by
  have h : kappa^[6] 0 = kappa (kappa (kappa (kappa (kappa (kappa 0))))) := rfl
  rw [h]
  exact kappa_le_step (a := 367981 / 500000) (r := 21157 / 31250) (c := 827089 / 1000000)
    (by linarith [kappa5_zero_ge]) kappa5_zero_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem kappa6_zero_le' : kappa^[6] 0 ≤ 7775 / 10000 :=
  kappa6_zero_le''.trans (by norm_num)

theorem kappa6_zero_le : kappa^[6] 0 ≤ 778 / 1000 :=
  kappa6_zero_le''.trans (by norm_num)

end kappa

end BstLean.Part139

open BstLean.Part139 in
#print axioms qform_sq_integral
open BstLean.Part139 in
#print axioms kappa6_zero_le
open BstLean.Part139 in
#print axioms kappa6_zero_le'
open BstLean.Part139 in
#print axioms covV_trace
open BstLean.Part139 in
#print axioms covV_frob_le
