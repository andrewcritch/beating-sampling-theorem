import BstLean.Part53Defs
import BstLean.Part48Defs
import BstLean.Part45DegDrop
import BstLean.Part36Index

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens TSymm contr fval varU Pcal uJ)
open BstLean.Part43 (varFQ)
open BstLean.Part48 (SBLevel)

variable {n d : ℕ}

private lemma dens_sph {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (h : DensLaw n μ Λ) : SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (BstLean.Part29.uniformSphere_ae_sphere n)

private lemma sphere_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f μ := by
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

private lemma map_smul (Z : CoefIdxD n d → ℝ) (l : ℝ) (x : Fin n → ℝ) :
    mapMD (l • Z) x = l • mapMD Z x := by
  funext a
  unfold mapMD BstLean.Part36.coefD
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  split_ifs <;> simp [mul_assoc]

private lemma contr_scale {j : ℕ} (A : (Fin j → Fin n) → ℝ)
    (l : ℝ) (y : Fin n → ℝ) :
    contr A (fun _ => l • y) = l ^ j * contr A (fun _ => y) := by
  unfold contr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private lemma pcal_cont (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    Continuous (Pcal k T Z) := by
  classical
  unfold Pcal uJ contr mapMD BstLean.Part36.coefD BstLean.Part36.monoVal
  fun_prop

lemma gaussian_variance_eq (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    varFQ μ k f0 T (sg n d • Z) = varU μ (Pcal k T Z) := by
  let := hμ.prob
  have hf : (fun x => fval k f0 T (mapMD (sg n d • Z) x)) =
      fun x => f0 + Pcal k T Z x := by
    funext x
    unfold fval Pcal uJ
    simp_rw [map_smul, contr_scale]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [sg, div_eq_mul_inv, mul_comm]
  unfold varFQ varU
  rw [hf]
  have hi := sphere_integrable hμ (pcal_cont k T Z)
  rw [integral_add (integrable_const f0) hi]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 1
  funext x
  congr 1
  ring

/-- The Gaussian event in the floor proof has the stated small-ball bound. -/
lemma gaussian_floor (d k : ℕ) (Λ : ℝ) (nF : ℕ) (hF : PropF53 d k Λ nF)
    (p t : ℝ) (hSB : SBLevel (2 * k) p t) (ht : 0 < t)
    (n : ℕ) (hn : nF ≤ n) (μ : Measure (Fin n → ℝ)) (hμ : DensLaw n μ Λ)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (hTk : 0 < BstLean.Part41.frob (T k)) :
    stdGauss (CoefIdxD n d) {Z | varFQ μ k f0 T (sg n d • Z) <
      4 * (t / 32) * Ncirc n d k f0 T} ≤ ENNReal.ofReal p := by
  have hS := dens_sph hμ
  obtain ⟨P, hdeg, hP⟩ := BstLean.Part45.var_poly45 (d := d) hS k T
  have heq (Z : CoefIdxD n d → ℝ) :
      MvPolynomial.eval Z P = varFQ μ k f0 T (sg n d • Z) := by
    rw [hP, gaussian_variance_eq μ hS]
  have hnonneg (Z : CoefIdxD n d → ℝ) : 0 ≤ MvPolynomial.eval Z P := by
    rw [hP]
    exact integral_nonneg fun _ => sq_nonneg _
  have hb := hSB (CoefIdxD n d) P hdeg hnonneg
  have hfloor := hF n hn μ hμ f0 T hT hTk
  have hlevel : 4 * (t / 32) * Ncirc n d k f0 T ≤
      t * ∫ Z, varFQ μ k f0 T (sg n d • Z) ∂stdGauss (CoefIdxD n d) := by
    nlinarith [mul_le_mul_of_nonneg_left hfloor ht.le]
  apply le_trans (measure_mono ?_) hb
  intro Z hZ
  change MvPolynomial.eval Z P < t * ∫ Z', MvPolynomial.eval Z' P
    ∂stdGauss (CoefIdxD n d)
  simp_rw [heq]
  exact lt_of_lt_of_le hZ hlevel

/-- The deterministic event inclusion used to transfer the floor to the sphere. -/
lemma floor_event_inclusion {Ω : Type*} (V V' R : Ω → ℝ) (A : Set Ω)
    (s N : ℝ) (hsN : 0 ≤ s * N)
    (hV : ∀ z ∈ A, 0 ≤ V z) (hV' : ∀ z ∈ A, 0 ≤ V' z)
    (hcomp : ∀ z ∈ A, Real.sqrt (V' z) ≤ Real.sqrt (V z) + R z) :
    {z | z ∈ A ∧ V z < s * N} ⊆
      {z | V' z < 4 * s * N} ∪ {z | Real.sqrt (s * N) ≤ R z} := by
  intro z hz
  by_cases hr : Real.sqrt (s * N) ≤ R z
  · exact Or.inr hr
  · apply Or.inl
    have hv := Real.sqrt_lt_sqrt (hV z hz.1) hz.2
    have hc := hcomp z hz.1
    have hr' : R z < Real.sqrt (s * N) := lt_of_not_ge hr
    have hsum : Real.sqrt (V' z) < 2 * Real.sqrt (s * N) := by linarith
    have hsq := Real.sq_sqrt (hV' z hz.1)
    have hsqN := Real.sq_sqrt hsN
    have hpos := Real.sqrt_nonneg (V' z)
    have hplus : 0 < 2 * Real.sqrt (s * N) + Real.sqrt (V' z) := by linarith
    have hprod := mul_pos (sub_pos.mpr hsum) hplus
    have hid : (2 * Real.sqrt (s * N) - Real.sqrt (V' z)) *
        (2 * Real.sqrt (s * N) + Real.sqrt (V' z)) =
        (2 * Real.sqrt (s * N)) ^ 2 - Real.sqrt (V' z) ^ 2 := by ring
    rw [hid] at hprod
    calc
      V' z = Real.sqrt (V' z) ^ 2 := hsq.symm
      _ < (2 * Real.sqrt (s * N)) ^ 2 := sub_pos.mp hprod
      _ = 4 * s * N := by rw [mul_pow, hsqN]; ring

/-- A radial tail bound, together with the Gaussian floor, gives the sphere floor. -/
lemma floor_transfer {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (V V' R : Ω → ℝ) (A : Set Ω) (s N p q : ℝ)
    (hsN : 0 ≤ s * N) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hV : ∀ z ∈ A, 0 ≤ V z) (hV' : ∀ z ∈ A, 0 ≤ V' z)
    (hcomp : ∀ z ∈ A, Real.sqrt (V' z) ≤ Real.sqrt (V z) + R z)
    (hgauss : ν {z | V' z < 4 * s * N} ≤ ENNReal.ofReal p)
    (hrad : ν {z | Real.sqrt (s * N) ≤ R z} ≤ ENNReal.ofReal q) :
    ν {z | z ∈ A ∧ V z < s * N} ≤ ENNReal.ofReal (p + q) := by
  calc
    ν {z | z ∈ A ∧ V z < s * N} ≤
        ν ({z | V' z < 4 * s * N} ∪ {z | Real.sqrt (s * N) ≤ R z}) :=
      measure_mono (floor_event_inclusion V V' R A s N hsN hV hV' hcomp)
    _ ≤ ν {z | V' z < 4 * s * N} + ν {z | Real.sqrt (s * N) ≤ R z} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal p + ENNReal.ofReal q := add_le_add hgauss hrad
    _ = ENNReal.ofReal (p + q) := (ENNReal.ofReal_add hp hq).symm

private lemma heat_top (k : ℕ) (v : ℝ) (A : Tens n) : heatA k v A k = A k := by
  funext w
  unfold heatA
  have hf : (Finset.range (k + 1)).filter (fun i => k + 2 * i ≤ k) = {0} := by
    ext i
    simp
  rw [hf, Finset.sum_singleton]
  have hfac : (k.factorial : ℝ) / k.factorial = 1 := div_self (by positivity)
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero,
    add_zero, hfac, one_mul]
  unfold BstLean.Part41.trL
  simp only [Finset.univ_unique, Finset.sum_singleton]
  congr 1

lemma Ncirc_positive (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (f0 : ℝ)
    (T : Tens n) (hTk : 0 < BstLean.Part41.frob (T k)) : 0 < Ncirc n d k f0 T := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have htop : BstLean.Part41.frob (Tcirc n d k f0 T k) = BstLean.Part41.frob (T k) := by
    unfold Tcirc
    rw [heat_top]
    congr 1
    funext w
    simp [TF, show k ≠ 0 by omega]
  unfold Ncirc
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (f := fun c => BstLean.Part41.frob (Tcirc n d k f0 T c) / DD n d ^ c)
    (fun c _ => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_pos hD c).le)
    (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩))
  rw [htop]
  exact div_pos hTk (pow_pos hD k)

end BstLean.Part53.T2Aux
