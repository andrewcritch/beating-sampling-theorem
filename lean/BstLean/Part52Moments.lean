import BstLean.Part52Expand

/-!
# Part 52, wave 3: the Gaussian moments of `Xc` and `Wc`

* `EX2_ge_one`: `1 ≤ E_Z Xc(Z)²`.
* `EW_le`: `E_Z Wc(Z) ≤ (d+1)^k` (`d ≥ 1`).
* `Xc_poly`: `Xc(Z)² = eval Z P`, `deg P ≤ 2k`.
* `Wc_integrable`, `Wc_nonneg`, `varU_le_Wc`, `Xc_zero`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part52

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD mapMD monoVal)
open BstLean.Part41 (Mono phiM phiSq varU)
open BstLean.Part40 (SphLaw)

variable {n d k : ℕ}

theorem EX2_eq {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n)
    (hι : Function.Injective ι) :
    ∫ Z, Xc μ ι Z ^ 2 ∂stdGauss (CoefIdxD n d) =
      ∑ b : Fin k → Mono n d, (∫ x, phB b x ∂μ) ^ 2 := by
  have h : ∀ Z : CoefIdxD n d → ℝ, Xc μ ι Z ^ 2 = ∑ b : Fin k → Mono n d, ∑ b' : Fin k → Mono n d,
      ((∫ x, phB b x ∂μ) * (∫ x, phB b' x ∂μ)) * (zB ι b Z * zB ι b' Z) := by
    intro Z
    rw [Xc_expand hμ, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro b' _
    ring
  simp_rw [h]
  rw [Ez_double ι hι]
  simp [sq]

theorem phB_default (x : Fin n → ℝ) : phB (fun _ : Fin k => (default : Mono n d)) x = 1 := by
  unfold phB
  apply Finset.prod_eq_one
  intro t _
  rfl

theorem EX2_ge_one {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n)
    (hι : Function.Injective ι) :
    1 ≤ ∫ Z, Xc μ ι Z ^ 2 ∂stdGauss (CoefIdxD n d) := by
  have := hμ.prob
  rw [EX2_eq hμ ι hι]
  have h0 : (∫ x, phB (fun _ : Fin k => (default : Mono n d)) x ∂μ) ^ 2 = 1 := by
    simp_rw [phB_default]; simp
  calc (1 : ℝ) = (∫ x, phB (fun _ : Fin k => (default : Mono n d)) x ∂μ) ^ 2 := h0.symm
    _ ≤ _ := Finset.single_le_sum (f := fun b : Fin k → Mono n d => (∫ x, phB b x ∂μ) ^ 2)
          (fun b _ => sq_nonneg _) (Finset.mem_univ _)

theorem sum_phB_sq (x : Fin n → ℝ) :
    ∑ b : Fin k → Mono n d, phB b x * phB b x = phiSq d x ^ k := by
  unfold phB phiSq
  rw [show (∑ p : Mono n d, phiM x p ^ 2) ^ k = ∏ _t : Fin k, ∑ p : Mono n d, phiM x p ^ 2 from
    (Fin.prod_const k _).symm, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  ring

theorem EW_eq {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n)
    (hι : Function.Injective ι) :
    ∫ Z, Wc μ ι Z ∂stdGauss (CoefIdxD n d) = ∫ x, phiSq d x ^ k ∂μ := by
  simp_rw [Wc_expand hμ ι]
  rw [Ez_double ι hι]
  rw [← integral_finsetSum _ (fun b _ => phB2_integrable hμ b b)]
  simp_rw [sum_phB_sq]

theorem EW_le {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (hd : 1 ≤ d) (ι : Fin k → Fin n)
    (hι : Function.Injective ι) :
    ∫ Z, Wc μ ι Z ∂stdGauss (CoefIdxD n d) ≤ ((d : ℝ) + 1) ^ k := by
  have := hμ.prob
  rw [EW_eq hμ ι hι]
  have hint : Integrable (fun x => phiSq d x ^ k) μ := by
    have hc : Continuous (fun x : Fin n → ℝ => phiSq d x ^ k) := by
      unfold phiSq
      exact (continuous_finsetSum _ (fun p _ =>
        (BstLean.Part49.continuous_monoVal _).pow 2)).pow k
    exact BstLean.Part49.sph_integrable hμ.sphere hc
  calc ∫ x, phiSq d x ^ k ∂μ ≤ ∫ _x, ((d : ℝ) + 1) ^ k ∂μ := by
        apply integral_mono_ae hint (integrable_const _)
        filter_upwards [hμ.sphere] with x hx
        have hb := BstLean.Part43.phiSq_bounds hd x hx
        exact pow_le_pow_left₀ (by linarith [hb.1]) hb.2 k
    _ = ((d : ℝ) + 1) ^ k := by simp

/-- The polynomial `Q` with `eval Z Q = Xc μ ι Z`. -/
noncomputable def XcQ (μ : Measure (Fin n → ℝ)) (ι : Fin k → Fin n) : MvPolynomial (CoefIdxD n d) ℝ :=
  ∑ b : Fin k → Mono n d, MvPolynomial.C (∫ x, phB b x ∂μ) * ∏ t, MvPolynomial.X (idx (b t) (ι t))

theorem eval_XcQ {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n)
    (Z : CoefIdxD n d → ℝ) : MvPolynomial.eval Z (XcQ μ ι) = Xc μ ι Z := by
  rw [Xc_expand hμ, XcQ]
  simp [zB]

theorem XcQ_degree (μ : Measure (Fin n → ℝ)) (ι : Fin k → Fin n) :
    (XcQ (d := d) μ ι).totalDegree ≤ k := by
  unfold XcQ
  apply MvPolynomial.totalDegree_finsetSum_le
  intro b _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  simp

theorem Xc_poly {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n) :
    ∃ P : MvPolynomial (CoefIdxD n d) ℝ, (∀ Z, Xc μ ι Z ^ 2 = MvPolynomial.eval Z P) ∧
      P.totalDegree ≤ 2 * k := by
  refine ⟨XcQ μ ι ^ 2, fun Z => by rw [map_pow, eval_XcQ hμ], ?_⟩
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have := XcQ_degree (d := d) μ ι
  exact Nat.mul_le_mul_left 2 this

theorem Wc_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n) :
    Integrable (Wc μ ι) (stdGauss (CoefIdxD n d)) := by
  have : Wc μ ι = fun Z => ∑ b : Fin k → Mono n d, ∑ b' : Fin k → Mono n d,
      (∫ x, phB b x * phB b' x ∂μ) * (zB ι b Z * zB ι b' Z) := funext (Wc_expand hμ ι)
  rw [this]
  exact integrable_finsetSum _ (fun b _ => integrable_finsetSum _
    (fun b' _ => (zB_pair_integrable ι b b').const_mul _))

theorem Wc_nonneg (μ : Measure (Fin n → ℝ)) (ι : Fin k → Fin n) (Z : CoefIdxD n d → ℝ) :
    0 ≤ Wc μ ι Z := integral_nonneg fun _ => sq_nonneg _

theorem varU_le_Wc {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n)
    (Z : CoefIdxD n d → ℝ) : varU μ (hZ ι Z) ≤ Wc μ ι Z := by
  have := hμ.prob
  have hc := hZ_continuous ι Z
  have hi : Integrable (hZ ι Z) μ := BstLean.Part49.sph_integrable hμ.sphere hc
  have hi2 : Integrable (fun x => hZ ι Z x ^ 2) μ :=
    BstLean.Part49.sph_integrable hμ.sphere (hc.pow 2)
  set m := ∫ x, hZ ι Z x ∂μ with hm
  have hexp : ∀ x, (hZ ι Z x - m) ^ 2 = hZ ι Z x ^ 2 - 2 * m * hZ ι Z x + m ^ 2 := fun x => by ring
  unfold varU Wc
  rw [← hm]
  simp_rw [hexp]
  have hA : Integrable (fun x => hZ ι Z x ^ 2 - 2 * m * hZ ι Z x) μ := hi2.sub (hi.const_mul (2 * m))
  have hB : Integrable (fun x => 2 * m * hZ ι Z x) μ := hi.const_mul (2 * m)
  rw [integral_add hA (integrable_const _), integral_sub hi2 hB, integral_const_mul, ← hm]
  simp
  nlinarith [sq_nonneg m]

theorem Xc_zero (μ : Measure (Fin n → ℝ)) (ι : Fin k → Fin n) (hk : 1 ≤ k) :
    Xc μ ι (0 : CoefIdxD n d → ℝ) = 0 := by
  unfold Xc hZ
  have : ∀ x, ∏ t, mapMD (0 : CoefIdxD n d → ℝ) x (ι t) = 0 := by
    intro x
    apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, hk⟩)
    simp [mapMD, BstLean.Part36.coefD]
  simp_rw [this]
  simp

end BstLean.Part52
