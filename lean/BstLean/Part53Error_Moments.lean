import BstLean.Part53Defs
import BstLean.Part43Floor

namespace BstLean.Part53

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (Mono phiM phiSq frob)
open BstLean.Part40 (SphLaw)

variable {n d : ℕ}

private lemma sphere_cont_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  let := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma dens_sph {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (h : DensLaw n μ Λ) :
    SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (BstLean.Part29.uniformSphere_ae_sphere n)

private lemma uniform_sph (hn : 1 ≤ n) : SphLaw n (uniformSphere n) :=
  ⟨BstLean.Part29.uniformSphere_isProbability n hn,
    BstLean.Part29.uniformSphere_ae_sphere n⟩

/-- The upper density bound transfers every continuous nonnegative moment. -/
theorem error53_density_moment {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hn : 1 ≤ n) (hμ : DensLaw n μ Λ) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂μ ≤ Real.exp Λ * ∫ x, f x ∂uniformSphere n := by
  obtain ⟨hp, ρ, hρ, hρ0, heq, hρbounds⟩ := hμ
  rw [heq, integral_withDensity_eq_integral_toReal_smul
    (hρ.ennreal_ofReal) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x => mul_nonneg (hρ0 x) (hf0 x)
  · exact (sphere_cont_integrable (uniform_sph hn) hf).const_mul _
  · filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact mul_le_mul_of_nonneg_right (hρbounds x hx).2 (hf0 x)

private lemma phi_cont (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) :=
  continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)

/-- Lemma G and the density bound control the nonconstant feature operator under `μ`. -/
theorem error53_feature_operator {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hn : 1 ≤ n) (hμ : DensLaw n μ Λ) (hG : LemmaG53 d)
    (a : Mono n d → ℝ) (ha : a default = 0) :
    ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂μ ≤
      (Real.exp Λ * cG d / n) * nsq a := by
  have hf : Continuous (fun x : Fin n → ℝ => (∑ p, a p * phiM x p) ^ 2) :=
    (continuous_finsetSum _ fun p _ => (phi_cont p).const_mul (a p)).pow 2
  calc
    _ ≤ Real.exp Λ * ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n :=
      error53_density_moment hn hμ hf (fun x => sq_nonneg _)
    _ ≤ Real.exp Λ * (cG d / n * nsq a) :=
      mul_le_mul_of_nonneg_left (hG n hn a ha) (Real.exp_pos _).le
    _ = _ := by ring

/-- An operator second-moment bound controls weighted means in Euclidean norm. -/
theorem error53_weighted_mean {ι : Type*} [Fintype ι]
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (r : ι → (Fin n → ℝ) → ℝ) (hr : ∀ p, Continuous (r p))
    (η : ℝ) (hη : 0 < η)
    (hop : ∀ a : ι → ℝ,
      ∫ x, (∑ p, a p * r p x) ^ 2 ∂μ ≤ η * ∑ p, a p ^ 2)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∑ p, (∫ x, r p x * F x ∂μ) ^ 2) ≤ η * ∫ x, F x ^ 2 ∂μ := by
  classical
  let b : ι → ℝ := fun p => ∫ x, r p x * F x ∂μ
  let L : (Fin n → ℝ) → ℝ := fun x => ∑ p, b p * r p x
  let S : ℝ := ∑ p, b p ^ 2
  have hL : Continuous L := continuous_finsetSum _ fun p _ => (hr p).const_mul _
  have hLF : ∫ x, L x * F x ∂μ = S := by
    simp only [L, Finset.sum_mul]
    rw [integral_finsetSum _ (fun p _ =>
      ((sphere_cont_integrable hμ ((hr p).mul hF)).const_mul (b p)).congr
        (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring))]
    simp only [mul_assoc, integral_const_mul, ← pow_two, b, S]
  have hineq : (2 * η) * S ≤ (∫ x, L x ^ 2 ∂μ) + η ^ 2 * ∫ x, F x ^ 2 ∂μ := by
    rw [← hLF, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (f := fun x => L x ^ 2) (g := fun x => η ^ 2 * F x ^ 2)
        (sphere_cont_integrable hμ (hL.pow 2))
        ((sphere_cont_integrable hμ (hF.pow 2)).const_mul _)]
    apply integral_mono
    · exact (sphere_cont_integrable hμ (hL.mul hF)).const_mul _
    · exact sphere_cont_integrable hμ ((hL.pow 2).add ((hF.pow 2).const_mul _))
    · intro x
      nlinarith [sq_nonneg (L x - η * F x)]
  have hb := hop b
  change (∫ x, L x ^ 2 ∂μ) ≤ η * S at hb
  have hscaled : η * S ≤ η * (η * ∫ x, F x ^ 2 ∂μ) := by
    nlinarith
  exact (le_of_mul_le_mul_left hscaled hη)

/-- Jensen's square inequality for continuous functions on a sphere probability law. -/
theorem error53_mean_square {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫ x, F x ∂μ) ^ 2 ≤ ∫ x, F x ^ 2 ∂μ := by
  let := hμ.prob
  have hop : ∀ a : Unit → ℝ,
      ∫ x, (∑ p : Unit, a p * (1 : ℝ)) ^ 2 ∂μ ≤ 1 * ∑ p : Unit, a p ^ 2 := by
    intro a
    simp
  simpa using error53_weighted_mean hμ (fun _ : Unit => fun _ => (1 : ℝ))
    (fun _ => continuous_const) 1 zero_lt_one hop F hF

private lemma phiSq_cont : Continuous (fun x : Fin n → ℝ => phiSq d x) :=
  continuous_finsetSum _ fun p _ => (phi_cont p).pow 2

private lemma p4_cont : Continuous (p4 (n := n)) :=
  continuous_finsetSum _ fun p _ => (continuous_apply p).pow 4

/-- Direct even trace moment bound for weighted tensor estimates. -/
theorem error53_trace_even_moment {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hn : 1 ≤ n) (hμ : DensLaw n μ Λ) (hU : LemmaU53 d) (hS : LemmaS53)
    (i : ℕ) (hi : 1 ≤ i) :
    (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤
      (d : ℝ) ^ (2 * i) * Real.exp Λ *
        ((8 * i - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * i) := by
  have hc : Continuous (fun x : Fin n → ℝ => phiSq d x - c0 d) :=
    phiSq_cont.sub continuous_const
  have hq : 1 ≤ 2 * i := by omega
  have heven (x : Fin n → ℝ) : 0 ≤ (phiSq d x - c0 d) ^ (2 * i) := by
    rw [Nat.mul_comm, pow_mul]
    exact sq_nonneg _
  have hpow : ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂uniformSphere n ≤
      (d : ℝ) ^ (2 * i) * ∫ x, p4 x ^ (2 * i) ∂uniformSphere n := by
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact sphere_cont_integrable (uniform_sph hn) (hc.pow _)
    · exact (sphere_cont_integrable (uniform_sph hn) (p4_cont.pow _)).const_mul _
    · filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      have hu := hU n x hx
      calc
        _ ≤ ((d : ℝ) * p4 x) ^ (2 * i) := pow_le_pow_left₀ hu.1 hu.2 _
        _ = _ := mul_pow _ _ _
  calc
    _ ≤ Real.exp Λ * ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂uniformSphere n :=
      error53_density_moment hn hμ (hc.pow _) heven
    _ ≤ Real.exp Λ * ((d : ℝ) ^ (2 * i) * ∫ x, p4 x ^ (2 * i) ∂uniformSphere n) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ ≤ Real.exp Λ * ((d : ℝ) ^ (2 * i) *
        (((4 * (2 * i) - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * i))) := by
      gcongr
      exact hS n hn (2 * i) hq
    _ = _ := by rw [show 4 * (2 * i) = 8 * i by omega]; ring

/-- The repaired trace moment bound retains only one density factor after squaring. -/
theorem error53_trace_moment {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hn : 1 ≤ n) (hμ : DensLaw n μ Λ) (hU : LemmaU53 d) (hS : LemmaS53)
    (i : ℕ) (hi : 1 ≤ i) :
    (∫ x, (phiSq d x - c0 d) ^ i ∂μ) ^ 2 ≤
      (d : ℝ) ^ (2 * i) * Real.exp Λ *
        ((8 * i - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * i) := by
  have hc : Continuous (fun x : Fin n → ℝ => phiSq d x - c0 d) :=
    phiSq_cont.sub continuous_const
  have hj := error53_mean_square (dens_sph hμ) _ (hc.pow i)
  simp only [Pi.pow_apply, ← pow_mul] at hj
  have hj' : (∫ x, (phiSq d x - c0 d) ^ i ∂μ) ^ 2 ≤
      ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ := by
    simpa [Nat.mul_comm] using hj
  exact hj'.trans (error53_trace_even_moment hn hμ hU hS i hi)

private lemma tensor_product_square_sum {ι : Type*} [Fintype ι] (c : ℕ) (v : ι → ℝ) :
    (∑ w : Fin c → ι, (∏ t, v (w t)) ^ 2) = (∑ p, v p ^ 2) ^ c := by
  classical
  induction c with
  | zero => simp
  | succ c ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (c + 1) => ι)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, mul_pow]
    simp_rw [← Finset.mul_sum, ih]
    rw [← Finset.sum_mul, pow_succ]
    ring

/-- A feature operator bound controls all mean tensor powers. -/
theorem error53_tensor_mean {ι : Type*} [Fintype ι]
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (u : ι → (Fin n → ℝ) → ℝ) (hu : ∀ p, Continuous (u p))
    (e : ι → ℝ) (he : ∑ p, e p ^ 2 = 1)
    (η R : ℝ) (hη : 0 < η) (hR : 1 ≤ R)
    (hbound : ∀ᵐ x ∂μ, ∑ p, u p x ^ 2 ≤ R)
    (hop : ∀ a : ι → ℝ,
      ∫ x, (∑ p, a p * (u p x - e p)) ^ 2 ∂μ ≤ η * ∑ p, a p ^ 2)
    (c : ℕ) :
    (∑ w : Fin c → ι, ((∫ x, ∏ t, u (w t) x ∂μ) - ∏ t, e (w t)) ^ 2) ≤
      (4 * R) ^ c * η := by
  classical
  let := hμ.prob
  let F (c : ℕ) (w : Fin c → ι) (x : Fin n → ℝ) : ℝ := ∏ t, u (w t) x
  let H (c : ℕ) (w : Fin c → ι) : ℝ := (∫ x, F c w x ∂μ) - ∏ t, e (w t)
  have hFc : ∀ c w, Continuous (F c w) := fun c w =>
    continuous_finsetProd _ fun t _ => hu (w t)
  have hmean (c : ℕ) (p : ι) (w : Fin c → ι) :
      H (c + 1) (Fin.cons p w) = e p * H c w +
        ∫ x, (u p x - e p) * F c w x ∂μ := by
    have hf (x : Fin n → ℝ) : F (c + 1) (Fin.cons p w) x =
        e p * F c w x + (u p x - e p) * F c w x := by
      simp only [F, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    simp only [H, hf, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [integral_add (f := fun x => e p * F c w x)
      (g := fun x => (u p x - e p) * F c w x)
      ((sphere_cont_integrable hμ (hFc c w)).const_mul _)
      (sphere_cont_integrable hμ (((hu p).sub continuous_const).mul (hFc c w))),
      integral_const_mul]
    ring
  have henergy (c : ℕ) :
      (∑ w : Fin c → ι, ∑ p,
        (∫ x, (u p x - e p) * F c w x ∂μ) ^ 2) ≤ η * R ^ c := by
    calc
      _ ≤ ∑ w : Fin c → ι, η * ∫ x, F c w x ^ 2 ∂μ := by
        apply Finset.sum_le_sum
        intro w _
        exact error53_weighted_mean hμ (fun p x => u p x - e p)
          (fun p => (hu p).sub continuous_const) η hη hop (F c w) (hFc c w)
      _ = η * ∫ x, ∑ w : Fin c → ι, F c w x ^ 2 ∂μ := by
        rw [← Finset.mul_sum, integral_finsetSum (f := fun w x => F c w x ^ 2) _ (fun w _ =>
          sphere_cont_integrable hμ ((hFc c w).pow 2))]
      _ = η * ∫ x, (∑ p, u p x ^ 2) ^ c ∂μ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => tensor_product_square_sum c (fun p => u p x)
      _ ≤ η * R ^ c := by
        have hi : (∫ x, (∑ p, u p x ^ 2) ^ c ∂μ) ≤ R ^ c := by
          have hi' : (∫ x, (∑ p, u p x ^ 2) ^ c ∂μ) ≤ ∫ _ : Fin n → ℝ, R ^ c ∂μ := by
            apply integral_mono_ae
            · exact sphere_cont_integrable hμ
                ((continuous_finsetSum _ fun p _ => (hu p).pow 2).pow c)
            · exact integrable_const _
            · filter_upwards [hbound] with x hx
              exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => sq_nonneg _) hx c
          simpa using hi'
        exact mul_le_mul_of_nonneg_left hi hη.le
  change (∑ w : Fin c → ι, H c w ^ 2) ≤ (4 * R) ^ c * η
  induction c with
  | zero => simp [H, F, hη.le]
  | succ c ih =>
    have hrec : (∑ w : Fin (c + 1) → ι, H (c + 1) w ^ 2) ≤
        2 * (∑ w : Fin c → ι, H c w ^ 2) + 2 * η * R ^ c := by
      rw [← (Fin.consEquiv (fun _ : Fin (c + 1) => ι)).sum_comp,
        Fintype.sum_prod_type]
      change (∑ p, ∑ w : Fin c → ι, H (c + 1) (Fin.cons p w) ^ 2) ≤ _
      simp_rw [hmean]
      calc
        _ ≤ ∑ p, ∑ w : Fin c → ι,
            (2 * (e p * H c w) ^ 2 +
              2 * (∫ x, (u p x - e p) * F c w x ∂μ) ^ 2) := by
          apply Finset.sum_le_sum
          intro p _
          apply Finset.sum_le_sum
          intro w _
          nlinarith [sq_nonneg (e p * H c w -
            ∫ x, (u p x - e p) * F c w x ∂μ)]
        _ = 2 * (∑ w : Fin c → ι, H c w ^ 2) +
            2 * (∑ w : Fin c → ι, ∑ p,
              (∫ x, (u p x - e p) * F c w x ∂μ) ^ 2) := by
          simp only [Finset.sum_add_distrib, mul_pow]
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, he, one_mul, Finset.sum_comm]
        _ ≤ _ := by linarith [henergy c]
    have hpow : R ^ c ≤ (4 * R) ^ c :=
      pow_le_pow_left₀ (by linarith) (by linarith) c
    have hnonneg : 0 ≤ (4 * R) ^ c * η := by positivity
    calc
      _ ≤ 2 * (∑ w : Fin c → ι, H c w ^ 2) + 2 * η * R ^ c := hrec
      _ ≤ 2 * ((4 * R) ^ c * η) + 2 * η * (4 * R) ^ c := by gcongr
      _ ≤ (4 * R) ^ (c + 1) * η := by
        rw [pow_succ]
        nlinarith [mul_nonneg hnonneg (show 0 ≤ R - 1 by linarith)]

/-- Jensen bounds a scalar-weighted feature tensor by its scalar second moment. -/
theorem error53_weighted_tensor_moment {ι : Type*} [Fintype ι]
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (u : ι → (Fin n → ℝ) → ℝ) (hu : ∀ p, Continuous (u p))
    (R : ℝ) (hbound : ∀ᵐ x ∂μ, ∑ p, u p x ^ 2 ≤ R)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (c : ℕ) :
    (∑ w : Fin c → ι, (∫ x, F x * ∏ t, u (w t) x ∂μ) ^ 2) ≤
      R ^ c * ∫ x, F x ^ 2 ∂μ := by
  classical
  have hprod (w : Fin c → ι) : Continuous (fun x => ∏ t, u (w t) x) :=
    continuous_finsetProd _ fun t _ => hu (w t)
  calc
    _ ≤ ∑ w : Fin c → ι, ∫ x, (F x * ∏ t, u (w t) x) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro w _
      exact error53_mean_square hμ _ (hF.mul (hprod w))
    _ = ∫ x, ∑ w : Fin c → ι, (F x * ∏ t, u (w t) x) ^ 2 ∂μ := by
      rw [integral_finsetSum (f := fun w x => (F x * ∏ t, u (w t) x) ^ 2) _
        (fun w _ => sphere_cont_integrable hμ ((hF.mul (hprod w)).pow 2))]
    _ = ∫ x, F x ^ 2 * (∑ p, u p x ^ 2) ^ c ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [mul_pow]
      rw [← Finset.mul_sum]
      congr 1
      exact tensor_product_square_sum c (fun p => u p x)
    _ ≤ ∫ x, R ^ c * F x ^ 2 ∂μ := by
      apply integral_mono_ae
      · exact sphere_cont_integrable hμ
          ((hF.pow 2).mul ((continuous_finsetSum _ fun p _ => (hu p).pow 2).pow c))
      · exact (sphere_cont_integrable hμ (hF.pow 2)).const_mul _
      · filter_upwards [hbound] with x hx
        have hpow := pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => sq_nonneg _) hx c
        nlinarith [sq_nonneg (F x)]
    _ = _ := integral_const_mul _ _

end BstLean.Part53
