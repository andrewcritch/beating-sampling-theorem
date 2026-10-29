import BstLean.Part84Defs
import BstLean.Part81Mean
import BstLean.Part81KD

/-!
# Part 84: the Fubini facts and the decorrelation bound of the Gaussian model

* `fubIface`: `FubIface n d`.
* `decorIface`: `DecorIface n d CF`, from the representation `RepIface n d` and the feature
  operator bound `FeatOp n d CF`.

`FW P lam W x` is a finite separable sum `Σ_k g_k(W) h_k(x)` (`Sep`), with every `g_k` a function
with all moments under the Gaussian and every `h_k` continuous. All exchanges of integrals are done
term by term.
-/

namespace BstLean.Part84

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part41 (frob Tens)
open BstLean.Part53 (heatA tinner)
open BstLean.Part78 (zv Good sph_int good_coord sep_int sep_swap sep_swap_two)
open BstLean.Part81 (JJ WIdx pf kap eD FeatOp cont_pf cont_kap_diag cont_kap_right one_le_eD
  kap_diag_lower)

variable {n d : ℕ}

/-! ## Separable form of `FW` -/

/-- `F W x = Σ_k g_k(W) h_k(x)`, a finite sum, `g_k` with all moments, `h_k` continuous. -/
def Sep (F : (WIdx n d → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (g : ι → (WIdx n d → ℝ) → ℝ) (h : ι → (Fin n → ℝ) → ℝ),
    (∀ k, Good (stdGauss (WIdx n d)) (g k)) ∧ (∀ k, Continuous (h k)) ∧
    ∀ W x, F W x = ∑ k, g k W * h k x

lemma Sep.const (a : ℝ) : Sep (n := n) (d := d) (fun _ _ => a) :=
  ⟨Unit, inferInstance, fun _ _ => a, fun _ _ => 1, fun _ => Good.const a,
    fun _ => continuous_const, fun W x => by simp⟩

lemma Sep.add {F G : (WIdx n d → ℝ) → (Fin n → ℝ) → ℝ} (hF : Sep F) (hG : Sep G) :
    Sep (fun W x => F W x + G W x) := by
  obtain ⟨ι, _, g, h, hg, hh, e⟩ := hF
  obtain ⟨ι', _, g', h', hg', hh', e'⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim g g', Sum.elim h h', ?_, ?_, ?_⟩
  · rintro (k | k)
    · exact hg k
    · exact hg' k
  · rintro (k | k)
    · exact hh k
    · exact hh' k
  · intro W x
    rw [Fintype.sum_sum_type]
    simp [e, e']

lemma Sep.mul {F G : (WIdx n d → ℝ) → (Fin n → ℝ) → ℝ} (hF : Sep F) (hG : Sep G) :
    Sep (fun W x => F W x * G W x) := by
  obtain ⟨ι, _, g, h, hg, hh, e⟩ := hF
  obtain ⟨ι', _, g', h', hg', hh', e'⟩ := hG
  refine ⟨ι × ι', inferInstance, fun kl W => g kl.1 W * g' kl.2 W,
    fun kl x => h kl.1 x * h' kl.2 x, fun kl => (hg kl.1).mul (hg' kl.2),
    fun kl => (hh kl.1).mul (hh' kl.2), ?_⟩
  intro W x
  show F W x * G W x = ∑ kl : ι × ι', (g kl.1 W * g' kl.2 W) * (h kl.1 x * h' kl.2 x)
  rw [e, e', Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma sep_FW (P : MvPolynomial (Fin n) ℝ) (lam : ℝ) : Sep (n := n) (d := d) (FW P lam) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : FW (n := n) (d := d) (MvPolynomial.C a) lam = fun _ _ => a := by
      funext W x; simp [FW]
    rw [h]; exact Sep.const a
  | add p q hp hq =>
    have h : FW (d := d) (p + q) lam = fun W x => FW p lam W x + FW q lam W x := by
      funext W x; simp [FW]
    rw [h]; exact hp.add hq
  | mul_X p i hp =>
    have h : FW (d := d) (p * MvPolynomial.X i) lam =
        fun W x => FW p lam W x * (lam * zv W (pf x) i) := by
      funext W x; simp [FW]
    rw [h]
    refine hp.mul ⟨JJ n d, inferInstance, fun q W => lam * W (q, i), fun q x => pf x q,
      fun q => (good_coord (q, i)).const_mul lam, fun q => cont_pf q, ?_⟩
    intro W x
    show lam * ∑ q : JJ n d, W (q, i) * pf x q = ∑ q : JJ n d, lam * W (q, i) * pf x q
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring

lemma sep_facts (hn : 1 ≤ n) {F : (WIdx n d → ℝ) → (Fin n → ℝ) → ℝ} (hF : Sep F) :
    (∀ W, Continuous (F W)) ∧
    Good (stdGauss (WIdx n d)) (fun W => ∫ x, F W x ∂uniformSphere n) ∧
    ∫ W, ∫ x, F W x ∂uniformSphere n ∂stdGauss (WIdx n d) =
      ∫ x, ∫ W, F W x ∂stdGauss (WIdx n d) ∂uniformSphere n ∧
    ∫ W, (∫ x, F W x ∂uniformSphere n) ^ 2 ∂stdGauss (WIdx n d) =
      ∫ x, ∫ y, ∫ W, F W x * F W y ∂stdGauss (WIdx n d) ∂uniformSphere n ∂uniformSphere n := by
  obtain ⟨ι, _, g, h, hg, hh, e⟩ := hF
  have hF : F = fun W x => ∑ k, g k W * h k x := by funext W x; exact e W x
  subst hF
  have hi : ∀ k, Integrable (h k) (uniformSphere n) := fun k => sph_int hn (hh k)
  refine ⟨fun W => continuous_finsetSum _ fun k _ => continuous_const.mul (hh k), ?_, ?_, ?_⟩
  · simp_rw [sep_int g h hi]
    exact Good.sum _ fun k _ => (hg k).mul_const _
  · exact sep_swap g h (fun k => (hg k).integrable) hi
  · exact sep_swap_two g h (fun k l => ((hg k).mul (hg l)).integrable) hi

/-- **Fubini facts.** -/
theorem fubIface (n d : ℕ) (hn : 1 ≤ n) : FubIface n d := by
  intro P lam
  obtain ⟨h1, h2, h3, _⟩ := sep_facts hn (sep_FW (d := d) P lam)
  exact ⟨fun W => sph_int hn (h1 W), h2.integrable, h3⟩

/-! ## The sphere and its square -/

lemma cube_of_sphere {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) :
    x ∈ Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

lemma prod_int (hn : 1 ≤ n) {φ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hφ : Continuous φ) :
    Integrable φ ((uniformSphere n).prod (uniformSphere n)) := by
  have := uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := fun _ : Fin n => (-1 : ℝ)) (b := fun _ => (1 : ℝ))).prod
    (isCompact_Icc (a := fun _ : Fin n => (-1 : ℝ)) (b := fun _ => (1 : ℝ)))).bddAbove_image
      hφ.norm.continuousOn
  apply Integrable.of_bound hφ.aestronglyMeasurable C
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (uniformSphere_ae_sphere n),
    Measure.quasiMeasurePreserving_snd.ae (uniformSphere_ae_sphere n)] with z h1 h2
  apply hC
  exact Set.mem_image_of_mem _ ⟨cube_of_sphere h1, cube_of_sphere h2⟩

lemma kap_nonneg (x : Fin n → ℝ) : 0 ≤ kap d x x :=
  Finset.sum_nonneg fun q _ => mul_self_nonneg _

lemma kap_symm (x y : Fin n → ℝ) : kap d x y = kap d y x :=
  Finset.sum_congr rfl fun q _ => mul_comm _ _

lemma kap_cs (x y : Fin n → ℝ) : kap d x y ^ 2 ≤ kap d x x * kap d y y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (JJ n d))
    (fun q => pf x q) (fun q => pf y q)
  have e : ∀ z : Fin n → ℝ, kap d z z = ∑ q : JJ n d, pf z q ^ 2 := fun z =>
    Finset.sum_congr rfl fun q _ => (sq _).symm
  rw [e x, e y]
  exact h

lemma kap2_int {CF : ℝ} (hF : FeatOp n d CF) (x : Fin n → ℝ) :
    ∫ y, kap d x y ^ 2 ∂uniformSphere n ≤ CF / (n : ℝ) * kap d x x := by
  have h := hF (fun q => pf x q)
  have e : ∑ q : JJ n d, pf x q ^ 2 = kap d x x :=
    Finset.sum_congr rfl fun q _ => sq _
  rw [e] at h
  exact h

lemma cont_kap2 : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kap d z.1 z.2) :=
  continuous_finsetSum _ fun q _ =>
    ((cont_pf q).comp continuous_fst).mul ((cont_pf q).comp continuous_snd)

lemma diag_step (hn : 1 ≤ n) (hd : 1 ≤ d) {u : (Fin n → ℝ) → ℝ} (hu : Continuous u)
    (hu0 : ∀ x, 0 ≤ u x) (j : ℕ) :
    ∫ x, u x * kap d x x ^ j ∂uniformSphere n ≤
      1 / eD d * ∫ x, u x * kap d x x ^ (j + 1) ∂uniformSphere n := by
  have he : 0 < eD d := lt_of_lt_of_le one_pos (one_le_eD d hd)
  rw [← integral_const_mul]
  apply integral_mono_ae (sph_int hn (hu.mul ((cont_kap_diag d).pow j)))
    ((sph_int hn (hu.mul ((cont_kap_diag d).pow (j + 1)))).const_mul _)
  filter_upwards [uniformSphere_ae_sphere n] with x hx
  have hk := kap_diag_lower n d x hx
  have hk0 : 0 ≤ kap d x x := le_trans he.le hk
  have h : u x * kap d x x ^ j * eD d ≤ u x * kap d x x ^ (j + 1) := by
    rw [pow_succ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hk (mul_nonneg (hu0 x) (pow_nonneg hk0 j))
  rw [one_div, inv_mul_eq_div, le_div_iff₀ he]
  exact h

lemma prod_split (hn : 1 ≤ n) {m : (Fin n → ℝ) → ℝ} {R : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hm : Continuous m) (hR : Continuous R) :
    ∫ x, ∫ y, (m x * m y + R (x, y)) ∂uniformSphere n ∂uniformSphere n =
      (∫ x, m x ∂uniformSphere n) ^ 2 + ∫ z, R z ∂((uniformSphere n).prod (uniformSphere n)) := by
  have hprob := uniformSphere_isProbability n hn
  have hmm : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => m z.1 * m z.2) :=
    (hm.comp continuous_fst).mul (hm.comp continuous_snd)
  have i1 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => m z.1 * m z.2)
      ((uniformSphere n).prod (uniformSphere n)) := prod_int hn hmm
  have i2 : Integrable R ((uniformSphere n).prod (uniformSphere n)) := prod_int hn hR
  have e := integral_prod (fun z : (Fin n → ℝ) × (Fin n → ℝ) => m z.1 * m z.2 + R z) (i1.add i2)
  have e2 := integral_add i1 i2
  have e3 := integral_prod_mul (μ := uniformSphere n) (ν := uniformSphere n) m m
  simp only at e
  rw [← e, e2, e3, sq]

lemma var_expand {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun w => f w * f w) μ) (a : ℝ) :
    ∫ w, (f w - a) ^ 2 ∂μ = ∫ w, f w * f w ∂μ - 2 * a * ∫ w, f w ∂μ + a ^ 2 := by
  have e : ∀ w, (f w - a) ^ 2 = f w * f w - (2 * a) * f w + a ^ 2 := by intro w; ring
  simp_rw [e]
  have e1 := integral_add (hf2.sub (hf.const_mul (2 * a))) (integrable_const (μ := μ) (a ^ 2))
  have e2 := integral_sub hf2 (hf.const_mul (2 * a))
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]

/-! ## Bessel form of the feature operator bound -/

lemma bessel (hn : 1 ≤ n) {CF : ℝ} (hCF : 0 ≤ CF) (hF : FeatOp n d CF)
    {r : (Fin n → ℝ) → ℝ} (hr : Continuous r) :
    ∑ q : JJ n d, (∫ x, r x * pf x q ∂uniformSphere n) ^ 2 ≤
      CF / (n : ℝ) * ∫ x, r x ^ 2 ∂uniformSphere n := by
  have := uniformSphere_isProbability n hn
  obtain ⟨c, hc⟩ : ∃ c : JJ n d → ℝ, ∀ q, c q = ∫ x, r x * pf x q ∂uniformSphere n :=
    ⟨_, fun _ => rfl⟩
  simp_rw [← hc]
  obtain ⟨L, hL⟩ : ∃ L : (Fin n → ℝ) → ℝ, ∀ x, L x = ∑ q, c q * pf x q := ⟨_, fun _ => rfl⟩
  have hLc : Continuous L := by
    have : L = fun x => ∑ q, c q * pf x q := funext hL
    rw [this]
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (cont_pf q)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ q, c q ^ 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ∫ x, r x ^ 2 ∂uniformSphere n := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∫ x, L x ^ 2 ∂uniformSphere n := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = CF / (n : ℝ) := ⟨_, rfl⟩
  rw [← hS, ← hR, ← ha]
  have hQa : Q ≤ a * S := by
    rw [hQ, ha, hS]
    simp_rw [hL]
    exact hF c
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun q _ => sq_nonneg _
  have hR0 : 0 ≤ R := by rw [hR]; exact integral_nonneg fun x => sq_nonneg _
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact integral_nonneg fun x => sq_nonneg _
  have hrp : ∀ q : JJ n d, Integrable (fun x => r x * pf x q) (uniformSphere n) :=
    fun q => sph_int hn (hr.mul (cont_pf q))
  have hr2 : Integrable (fun x => r x ^ 2) (uniformSphere n) := sph_int hn (hr.pow 2)
  have hrL : Integrable (fun x => r x * L x) (uniformSphere n) := sph_int hn (hr.mul hLc)
  have hL2 : Integrable (fun x => L x ^ 2) (uniformSphere n) := sph_int hn (hLc.pow 2)
  have hcross : ∫ x, r x * L x ∂uniformSphere n = S := by
    have h : ∀ x, r x * L x = ∑ q, c q * (r x * pf x q) := by
      intro x
      rw [hL, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    simp_rw [h]
    rw [integral_finsetSum _ fun q _ => (hrp q).const_mul _]
    simp_rw [integral_const_mul, ← hc]
    rw [hS]
    exact Finset.sum_congr rfl fun q _ => by rw [sq]
  have key : ∀ t : ℝ, 0 ≤ R - 2 * t * S + t ^ 2 * Q := by
    intro t
    have h0 : 0 ≤ ∫ x, (r x - t * L x) ^ 2 ∂uniformSphere n :=
      integral_nonneg fun x => sq_nonneg _
    have e : ∀ x, (r x - t * L x) ^ 2 = r x ^ 2 - (2 * t) * (r x * L x) + t ^ 2 * L x ^ 2 := by
      intro x; ring
    simp_rw [e] at h0
    have e1 := integral_add (hr2.sub (hrL.const_mul (2 * t))) (hL2.const_mul (t ^ 2))
    have e2 := integral_sub hr2 (hrL.const_mul (2 * t))
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, integral_const_mul, integral_const_mul, hcross, ← hR, ← hQ] at h0
    exact h0
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg hCF (Nat.cast_nonneg n)
  rcases ha0.eq_or_lt with h | h
  · rw [← h, zero_mul] at hQa ⊢
    by_contra hcon
    rw [not_le] at hcon
    have hk := key ((R + 1) / S)
    have hQ' : Q = 0 := le_antisymm hQa hQ0
    rw [hQ', mul_zero, add_zero, mul_assoc, div_mul_cancel₀ _ hcon.ne'] at hk
    linarith
  · have hk := key (1 / a)
    have h2 : (1 / a) ^ 2 * Q ≤ (1 / a) * S := by
      have h3 : (1 / a) ^ 2 * Q ≤ (1 / a) ^ 2 * (a * S) :=
        mul_le_mul_of_nonneg_left hQa (sq_nonneg _)
      have e : (1 / a) ^ 2 * (a * S) = 1 / a * S := by field_simp
      linarith
    have h3 : 0 ≤ R - 1 / a * S := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 h.le
    have e : a * (R - 1 / a * S) = a * R - S := by field_simp
    linarith

/-! ## One chaos level -/

lemma term_bound (hn : 1 ≤ n) (hd : 1 ≤ d) {CF : ℝ} (hCF : 0 ≤ CF) (hF : FeatOp n d CF)
    {I : Type*} [Fintype I] (G : I → (Fin n → ℝ) → ℝ) (hG : ∀ w, Continuous (G w))
    (c : ℕ) (hc : 1 ≤ c) :
    ∫ z, (∑ w, G w z.1 * G w z.2) * kap d z.1 z.2 ^ c
        ∂((uniformSphere n).prod (uniformSphere n)) ≤
      CF / (eD d * n) * ∫ x, (∑ w, G w x * G w x) * kap d x x ^ c ∂uniformSphere n := by
  have hprob := uniformSphere_isProbability n hn
  have he : 0 < eD d := lt_of_lt_of_le one_pos (one_le_eD d hd)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 ≤ CF / (n : ℝ) := div_nonneg hCF hn'.le
  have hCC : CF / (eD d * n) = CF / n * (1 / eD d) := by field_simp
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ, ∀ x, f x = ∑ w, G w x * G w x := ⟨_, fun _ => rfl⟩
  have hfc : Continuous f := by
    have : f = fun x => ∑ w, G w x * G w x := funext hf
    rw [this]
    exact continuous_finsetSum _ fun w _ => (hG w).mul (hG w)
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    rw [hf]; exact Finset.sum_nonneg fun w _ => mul_self_nonneg _
  simp_rw [← hf]
  have hkc := cont_kap2 (n := n) (d := d)
  have htc : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ∑ w, G w z.1 * G w z.2) :=
    continuous_finsetSum _ fun w _ =>
      ((hG w).comp continuous_fst).mul ((hG w).comp continuous_snd)
  obtain rfl | ⟨j, rfl⟩ : c = 1 ∨ ∃ j, c = j + 2 := by
    rcases c with _ | _ | j
    · omega
    · left; rfl
    · right; exact ⟨j, rfl⟩
  · -- the first chaos: Bessel
    have e1 : ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
        (∑ w, G w z.1 * G w z.2) * kap d z.1 z.2 ^ 1 =
          ∑ w, ∑ q : JJ n d, (G w z.1 * pf z.1 q) * (G w z.2 * pf z.2 q) := by
      intro z
      rw [pow_one, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold kap
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hi : ∀ (w : I) (q : JJ n d), Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (G w z.1 * pf z.1 q) * (G w z.2 * pf z.2 q))
        ((uniformSphere n).prod (uniformSphere n)) := fun w q =>
      prod_int hn ((((hG w).mul (cont_pf q)).comp continuous_fst).mul
        (((hG w).mul (cont_pf q)).comp continuous_snd))
    simp_rw [e1]
    rw [integral_finsetSum _ fun w _ => integrable_finsetSum _ fun q _ => hi w q]
    have e2 : ∀ w, ∫ z : (Fin n → ℝ) × (Fin n → ℝ),
        ∑ q : JJ n d, (G w z.1 * pf z.1 q) * (G w z.2 * pf z.2 q)
          ∂((uniformSphere n).prod (uniformSphere n)) =
        ∑ q : JJ n d, (∫ x, G w x * pf x q ∂uniformSphere n) ^ 2 := by
      intro w
      rw [integral_finsetSum _ fun q _ => hi w q]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [sq]
      exact integral_prod_mul (fun x => G w x * pf x q) (fun x => G w x * pf x q)
    simp_rw [e2]
    calc ∑ w, ∑ q : JJ n d, (∫ x, G w x * pf x q ∂uniformSphere n) ^ 2
        ≤ ∑ w, CF / (n : ℝ) * ∫ x, G w x ^ 2 ∂uniformSphere n :=
          Finset.sum_le_sum fun w _ => bessel hn hCF hF (hG w)
      _ = CF / (n : ℝ) * ∫ x, f x * kap d x x ^ 0 ∂uniformSphere n := by
          have hG2 : ∀ w, Integrable (fun x => G w x ^ 2) (uniformSphere n) :=
            fun w => sph_int hn ((hG w).pow 2)
          rw [← Finset.mul_sum, ← integral_finsetSum _ fun w _ => hG2 w]
          congr 1
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show ∑ w, G w x ^ 2 = f x * kap d x x ^ 0
          rw [pow_zero, mul_one, hf]
          exact Finset.sum_congr rfl fun w _ => sq _
      _ ≤ CF / (n : ℝ) * (1 / eD d * ∫ x, f x * kap d x x ^ (0 + 1) ∂uniformSphere n) :=
          mul_le_mul_of_nonneg_left (diag_step hn hd hfc hf0 0) ha0
      _ = _ := by rw [hCC, zero_add]; ring
  · -- higher chaoses: Cauchy–Schwarz and the Hilbert–Schmidt bound
    obtain ⟨U, hU⟩ : ∃ U : (Fin n → ℝ) → ℝ, ∀ x, U x = f x * kap d x x ^ j := ⟨_, fun _ => rfl⟩
    have hUc : Continuous U := by
      have : U = fun x => f x * kap d x x ^ j := funext hU
      rw [this]
      exact hfc.mul ((cont_kap_diag d).pow j)
    have hU0 : ∀ x, 0 ≤ U x := fun x => by
      rw [hU]; exact mul_nonneg (hf0 x) (pow_nonneg (kap_nonneg x) j)
    have pw : ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
        (∑ w, G w z.1 * G w z.2) * kap d z.1 z.2 ^ (j + 2) ≤
          1 / 2 * (kap d z.1 z.2 ^ 2 * U z.1) + 1 / 2 * (kap d z.2 z.1 ^ 2 * U z.2) := by
      rintro ⟨x, y⟩
      show (∑ w, G w x * G w y) * kap d x y ^ (j + 2) ≤
        1 / 2 * (kap d x y ^ 2 * U x) + 1 / 2 * (kap d y x ^ 2 * U y)
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ∑ w, G w x * G w y := ⟨_, rfl⟩
      rw [← ht]
      have ht2 : t ^ 2 ≤ f x * f y := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
          (fun w => G w x) (fun w => G w y)
        have e : ∀ z : Fin n → ℝ, f z = ∑ w, G w z ^ 2 := fun z => by
          rw [hf]; exact Finset.sum_congr rfl fun w _ => (sq _).symm
        rw [ht, e x, e y]
        exact h
      have hk : kap d x y ^ 2 ≤ kap d x x * kap d y y := kap_cs x y
      have hsq : (t * kap d x y ^ j) ^ 2 ≤ U x * U y := by
        calc (t * kap d x y ^ j) ^ 2 = t ^ 2 * (kap d x y ^ 2) ^ j := by ring
          _ ≤ (f x * f y) * (kap d x x * kap d y y) ^ j :=
              mul_le_mul ht2 (pow_le_pow_left₀ (sq_nonneg _) hk j)
                (pow_nonneg (sq_nonneg _) j) (mul_nonneg (hf0 x) (hf0 y))
          _ = U x * U y := by rw [hU, hU]; ring
      have h4 : (t * kap d x y ^ j) ^ 2 ≤ ((U x + U y) / 2) ^ 2 := by
        nlinarith [sq_nonneg (U x - U y)]
      have h5 : t * kap d x y ^ j ≤ (U x + U y) / 2 :=
        (abs_le_of_sq_le_sq' h4 (by have := hU0 x; have := hU0 y; linarith)).2
      rw [kap_symm y x]
      calc t * kap d x y ^ (j + 2) = (t * kap d x y ^ j) * kap d x y ^ 2 := by ring
        _ ≤ (U x + U y) / 2 * kap d x y ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
        _ = _ := by ring
    have i1 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kap d z.1 z.2 ^ 2 * U z.1)
        ((uniformSphere n).prod (uniformSphere n)) :=
      prod_int hn ((hkc.pow 2).mul (hUc.comp continuous_fst))
    have i2 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kap d z.2 z.1 ^ 2 * U z.2)
        ((uniformSphere n).prod (uniformSphere n)) := i1.swap
    have A1 : ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kap d z.1 z.2 ^ 2 * U z.1
          ∂((uniformSphere n).prod (uniformSphere n)) ≤
        CF / (n : ℝ) * ∫ x, f x * kap d x x ^ (j + 1) ∂uniformSphere n := by
      rw [integral_prod _ i1]
      have h : ∀ x : Fin n → ℝ, ∫ y, kap d x y ^ 2 * U x ∂uniformSphere n =
          U x * ∫ y, kap d x y ^ 2 ∂uniformSphere n := by
        intro x; rw [integral_mul_const, mul_comm]
      simp only [h]
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun x => mul_nonneg (hU0 x) (integral_nonneg fun y => sq_nonneg _)
      · exact (sph_int hn (hfc.mul ((cont_kap_diag d).pow (j + 1)))).const_mul _
      · refine ae_of_all _ fun x => ?_
        have h6 := mul_le_mul_of_nonneg_left (kap2_int hF x) (hU0 x)
        calc U x * ∫ y, kap d x y ^ 2 ∂uniformSphere n
            ≤ U x * (CF / (n : ℝ) * kap d x x) := h6
          _ = CF / (n : ℝ) * (f x * kap d x x ^ (j + 1)) := by rw [hU]; ring
    have A2 : ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kap d z.2 z.1 ^ 2 * U z.2
          ∂((uniformSphere n).prod (uniformSphere n)) =
        ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kap d z.1 z.2 ^ 2 * U z.1
          ∂((uniformSphere n).prod (uniformSphere n)) :=
      integral_prod_swap (fun z : (Fin n → ℝ) × (Fin n → ℝ) => kap d z.1 z.2 ^ 2 * U z.1)
    calc ∫ z : (Fin n → ℝ) × (Fin n → ℝ), (∑ w, G w z.1 * G w z.2) * kap d z.1 z.2 ^ (j + 2)
          ∂((uniformSphere n).prod (uniformSphere n))
        ≤ ∫ z : (Fin n → ℝ) × (Fin n → ℝ),
            (1 / 2 * (kap d z.1 z.2 ^ 2 * U z.1) + 1 / 2 * (kap d z.2 z.1 ^ 2 * U z.2))
            ∂((uniformSphere n).prod (uniformSphere n)) :=
          integral_mono (prod_int hn (htc.mul (hkc.pow _)))
            ((i1.const_mul _).add (i2.const_mul _)) pw
      _ = 1 / 2 * ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kap d z.1 z.2 ^ 2 * U z.1
            ∂((uniformSphere n).prod (uniformSphere n)) +
          1 / 2 * ∫ z : (Fin n → ℝ) × (Fin n → ℝ), kap d z.2 z.1 ^ 2 * U z.2
            ∂((uniformSphere n).prod (uniformSphere n)) := by
          rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ CF / (n : ℝ) * ∫ x, f x * kap d x x ^ (j + 1) ∂uniformSphere n := by
          rw [A2]; linarith
      _ ≤ CF / (n : ℝ) * (1 / eD d * ∫ x, f x * kap d x x ^ (j + 1 + 1) ∂uniformSphere n) :=
          mul_le_mul_of_nonneg_left (diag_step hn hd hfc hf0 (j + 1)) ha0
      _ = _ := by rw [hCC]; ring

/-! ## The chaos expansion of the two-point function -/

/-- One level of the two-point function. -/
noncomputable def Tc (d K : ℕ) (lam : ℝ) (A : Tens n) (c : ℕ) (x y : Fin n → ℝ) : ℝ :=
  tinner (heatA K (lam ^ 2 * kap d x x) A c) (heatA K (lam ^ 2 * kap d y y) A c) * kap d x y ^ c

/-- The covariance kernel `E_W F_x F_y − m_x m_y`. -/
noncomputable def Rr (d K : ℕ) (lam : ℝ) (A : Tens n) (x y : Fin n → ℝ) : ℝ :=
  ∑ c ∈ Finset.range K, (((c + 1).factorial : ℝ) * lam ^ (2 * (c + 1))) * Tc d K lam A (c + 1) x y

lemma cont_heatA (K : ℕ) (A : Tens n) (c : ℕ) (w : Fin c → Fin n) :
    Continuous (fun v : ℝ => heatA K v A c w) := by
  unfold heatA
  fun_prop

lemma cont_heat_x (d K : ℕ) (lam : ℝ) (A : Tens n) (c : ℕ) (w : Fin c → Fin n) :
    Continuous (fun x : Fin n → ℝ => heatA K (lam ^ 2 * kap d x x) A c w) :=
  (cont_heatA K A c w).comp (continuous_const.mul (cont_kap_diag d))

lemma cont_Tc (d K : ℕ) (lam : ℝ) (A : Tens n) (c : ℕ) :
    Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Tc d K lam A c z.1 z.2) := by
  unfold Tc tinner
  exact (continuous_finsetSum _ fun w _ =>
    ((cont_heat_x d K lam A c w).comp continuous_fst).mul
      ((cont_heat_x d K lam A c w).comp continuous_snd)).mul (cont_kap2.pow c)

lemma cont_Tc_diag (d K : ℕ) (lam : ℝ) (A : Tens n) (c : ℕ) :
    Continuous (fun x : Fin n → ℝ => Tc d K lam A c x x) := by
  unfold Tc tinner
  exact (continuous_finsetSum _ fun w _ =>
    (cont_heat_x d K lam A c w).mul (cont_heat_x d K lam A c w)).mul ((cont_kap_diag d).pow c)

lemma two_split (d K : ℕ) (lam : ℝ) (A : Tens n) (x y : Fin n → ℝ) :
    ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lam ^ (2 * c) *
        tinner (heatA K (lam ^ 2 * kap d x x) A c) (heatA K (lam ^ 2 * kap d y y) A c) *
        kap d x y ^ c =
      hmean K (lam ^ 2 * kap d x x) A * hmean K (lam ^ 2 * kap d y y) A + Rr d K lam A x y := by
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · have hu : ∀ w : Fin 0 → Fin n, w = fun i => i.elim0 := fun w => Subsingleton.elim _ _
    unfold tinner hmean
    rw [Fintype.sum_eq_single (fun i : Fin 0 => i.elim0) (fun w hw => absurd (hu w) hw)]
    simp
  · unfold Rr Tc
    exact Finset.sum_congr rfl fun c _ => by ring

lemma rr_bound (hn : 1 ≤ n) (hd : 1 ≤ d) {CF : ℝ} (hCF : 0 ≤ CF) (hF : FeatOp n d CF)
    (K : ℕ) (lam : ℝ) (A : Tens n) :
    ∫ z : (Fin n → ℝ) × (Fin n → ℝ), Rr d K lam A z.1 z.2
        ∂((uniformSphere n).prod (uniformSphere n)) ≤
      CF / (eD d * n) * ∫ x, Rr d K lam A x x ∂uniformSphere n := by
  have hprob := uniformSphere_isProbability n hn
  have hd1 : ∀ c, Integrable (fun x : Fin n → ℝ => Tc d K lam A c x x) (uniformSphere n) :=
    fun c => sph_int hn (cont_Tc_diag d K lam A c)
  unfold Rr
  rw [integral_finsetSum _ (fun c _ => (prod_int hn (cont_Tc d K lam A (c + 1))).const_mul _),
    integral_finsetSum _ (fun c _ => (hd1 (c + 1)).const_mul _), Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [integral_const_mul, integral_const_mul, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg _) ?_)
  · have tb := term_bound hn hd hCF hF (fun w x => heatA K (lam ^ 2 * kap d x x) A (c + 1) w)
      (fun w => cont_heat_x d K lam A (c + 1) w) (c + 1) (by omega)
    unfold Tc tinner
    exact tb
  · rw [pow_mul]; positivity


/-- **Decorrelation.** -/
theorem decorIface (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (CF : ℝ) (hCF : 0 ≤ CF)
    (hRep : RepIface n d) (hF : FeatOp n d CF) : DecorIface n d CF := by
  intro K P hP lam
  have hprob := uniformSphere_isProbability n hn
  obtain ⟨A, -, -, hmean1, htwo⟩ := hRep K P hP
  obtain ⟨-, gB0, hswap, htwoswap⟩ := sep_facts hn (sep_FW (d := d) P lam)
  have gB : Good (stdGauss (WIdx n d)) (fun W => BW P lam W) := gB0
  have hm : ∀ x, ∫ W : WIdx n d → ℝ, FW P lam W x ∂stdGauss (WIdx n d) =
      hmean K (lam ^ 2 * kap d x x) A := fun x => (hmean1 lam x).2
  have h2 : ∀ x y, ∫ W : WIdx n d → ℝ, FW P lam W x * FW P lam W y ∂stdGauss (WIdx n d) =
      hmean K (lam ^ 2 * kap d x x) A * hmean K (lam ^ 2 * kap d y y) A + Rr d K lam A x y :=
    fun x y => by rw [(htwo lam x y).2, two_split]
  have hmc : Continuous (fun x : Fin n → ℝ => hmean K (lam ^ 2 * kap d x x) A) :=
    cont_heat_x d K lam A 0 _
  have hRc : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Rr d K lam A z.1 z.2) := by
    unfold Rr
    exact continuous_finsetSum _ fun c _ => continuous_const.mul (cont_Tc d K lam A (c + 1))
  -- the mean of `B`
  have hμ : ∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d) =
      ∫ x, hmean K (lam ^ 2 * kap d x x) A ∂uniformSphere n :=
    hswap.trans (integral_congr_ae (ae_of_all _ hm))
  -- the second moment of `B`
  have hB2 : ∫ W : WIdx n d → ℝ, BW P lam W ^ 2 ∂stdGauss (WIdx n d) =
      (∫ x, hmean K (lam ^ 2 * kap d x x) A ∂uniformSphere n) ^ 2 +
        ∫ z : (Fin n → ℝ) × (Fin n → ℝ), Rr d K lam A z.1 z.2
          ∂((uniformSphere n).prod (uniformSphere n)) := by
    have h : ∫ W : WIdx n d → ℝ, BW P lam W ^ 2 ∂stdGauss (WIdx n d) =
        ∫ x, ∫ y, (hmean K (lam ^ 2 * kap d x x) A * hmean K (lam ^ 2 * kap d y y) A +
          Rr d K lam A x y) ∂uniformSphere n ∂uniformSphere n := by
      refine htwoswap.trans ?_
      simp_rw [h2]
    exact h.trans (prod_split hn hmc hRc)
  -- the left side
  obtain ⟨μB, hμB⟩ : ∃ μB : ℝ, μB = ∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d) :=
    ⟨_, rfl⟩
  rw [← hμB]
  have hL : ∫ W : WIdx n d → ℝ, (BW P lam W - μB) ^ 2 ∂stdGauss (WIdx n d) =
      ∫ z : (Fin n → ℝ) × (Fin n → ℝ), Rr d K lam A z.1 z.2
        ∂((uniformSphere n).prod (uniformSphere n)) := by
    have gB2 : Integrable (fun W : WIdx n d → ℝ => BW P lam W * BW P lam W)
        (stdGauss (WIdx n d)) := (gB.mul gB).integrable
    rw [var_expand (stdGauss (WIdx n d)) gB.integrable gB2 μB, ← hμB]
    simp_rw [← sq]
    rw [hB2, ← hμ, ← hμB]
    ring
  -- the right side
  have hRx : ∀ x : Fin n → ℝ, ∫ W : WIdx n d → ℝ,
      (FW P lam W x - ∫ W' : WIdx n d → ℝ, FW P lam W' x ∂stdGauss (WIdx n d)) ^ 2
        ∂stdGauss (WIdx n d) = Rr d K lam A x x := by
    intro x
    rw [hm x]
    obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = hmean K (lam ^ 2 * kap d x x) A := ⟨_, rfl⟩
    rw [← hmx]
    rw [var_expand (stdGauss (WIdx n d)) (hmean1 lam x).1 (htwo lam x x).1 mx, h2 x x, hm x,
      ← hmx]
    ring
  refine ⟨((gB.sub (Good.const μB)).pow 2).integrable, ?_⟩
  rw [hL]
  simp_rw [hRx]
  exact rr_bound hn hd hCF hF K lam A

end BstLean.Part84
