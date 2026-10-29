import BstLean.Part90Defs

/-!
# Part 90: `cubVarM`, the variance bound for the within-slice variance of a cubic

From the abstract slice bound (`CubSliceA`) and the single-point Wick variance (`VarWC`) to the
bound for `Vdn = E_p Y_p` in the slice model of Part 86 (`CubVarM`).

* `cubSliceM`: for almost every slice `p`, `Var_W Y_p ≤ (kY Ȳ_p + kE e0)²` and the floor
  `(1 − Λ) · 6 (c² τ2_p)³ ‖T‖_F² ≤ Ȳ_p`.
* `cubVarM`: pairs of slices, Cauchy–Schwarz, and the global floor.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part56 (integrable_cont_sph56)
open BstLean.Part78 (nsq frobH zv)
open BstLean.Part80 (kA FeatOpA)
open BstLean.Part82 (T3 SymT frobT trT cfun aU3 HU3)
open BstLean.Part86 BstLean.Part86.XGauss
open BstLean.Part89 (Ybar SliceOpF Ybar_eq Ybar_nonneg)

namespace VarM

/-! ## Continuity in `x` -/

section cont
variable {n : ℕ} {J : Type} [Fintype J]
variable {mu : (Fin n → ℝ) → Fin n → ℝ} {ψ : (Fin n → ℝ) → J → ℝ}

lemma c_mu (hmu : Continuous mu) (i : Fin n) : Continuous fun x => mu x i :=
  (continuous_apply i).comp hmu

lemma c_ps (hψ : Continuous ψ) (q : J) : Continuous fun x => ψ x q :=
  (continuous_apply q).comp hψ

lemma c_kA (hψ : Continuous ψ) : Continuous (kA ψ) :=
  continuous_finsetSum _ fun q _ => (c_ps hψ q).pow 2

lemma c_zv (hψ : Continuous ψ) (W : J × Fin n → ℝ) (i : Fin n) :
    Continuous fun x => zv W (ψ x) i :=
  continuous_finsetSum _ fun q _ => continuous_const.mul (c_ps hψ q)

lemma c_FC (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (hmu : Continuous mu) (hψ : Continuous ψ) (W : J × Fin n → ℝ) :
    Continuous (FC f0 ℓ H T mu ψ W) := by
  have hy (i : Fin n) : Continuous fun x => mu x i + zv W (ψ x) i :=
    (c_mu hmu i).add (c_zv hψ W i)
  show Continuous fun x => cfun f0 ℓ H T (fun i => mu x i + zv W (ψ x) i)
  unfold cfun
  refine ((continuous_const.add ?_).add ?_).add ?_
  · exact continuous_finsetSum _ fun i _ => continuous_const.mul (hy i)
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (hy i)).mul (hy j)
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => ((continuous_const.mul (hy i)).mul (hy j)).mul (hy k)

lemma c_AxC (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (hmu : Continuous mu) (hψ : Continuous ψ) (i : Fin n) :
    Continuous fun x => AxC ℓ H T mu ψ x i := by
  unfold AxC aU3
  refine ((continuous_const.add (continuous_const.mul ?_)).add (continuous_const.mul ?_)).add
    ((continuous_const.mul (c_kA hψ)).mul continuous_const)
  · exact continuous_finsetSum _ fun j _ => continuous_const.mul (c_mu hmu j)
  · exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      (continuous_const.mul (c_mu hmu j)).mul (c_mu hmu k)

lemma c_HxC (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hmu : Continuous mu) (i j : Fin n) :
    Continuous fun x => HxC H T mu x i j := by
  show Continuous fun x => H i j + 3 * ∑ k, T i j k * mu x k
  exact continuous_const.add (continuous_const.mul
    (continuous_finsetSum _ fun k _ => continuous_const.mul (c_mu hmu k)))

lemma c_wC (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (hmu : Continuous mu) (hψ : Continuous ψ) : Continuous (wC ℓ H T mu ψ) := by
  unfold wC nsq frobH
  refine (((c_kA hψ).mul ?_).add ((continuous_const.mul ((c_kA hψ).pow 2)).mul ?_)).add
    ((continuous_const.mul ((c_kA hψ).pow 3)).mul continuous_const)
  · exact continuous_finsetSum _ fun i _ => (c_AxC ℓ H T hmu hψ i).pow 2
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (c_HxC H T hmu i j).pow 2

lemma c_oscA (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (hmu : Continuous mu) (hψ : Continuous ψ) (Abar : Fin n → ℝ) :
    Continuous fun x => (nsq (fun i => AxC ℓ H T mu ψ x i - Abar i)) ^ 2 := by
  unfold nsq
  exact (continuous_finsetSum _ fun i _ =>
    ((c_AxC ℓ H T hmu hψ i).sub continuous_const).pow 2).pow 2

lemma c_oscH (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hmu : Continuous mu)
    (Hbar : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun x => (frobH (HxC H T mu x - Hbar)) ^ 2 := by
  unfold frobH
  simp only [Matrix.sub_apply]
  exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((c_HxC H T hmu i j).sub continuous_const).pow 2).pow 2

lemma wC_ge (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (mu : (Fin n → ℝ) → Fin n → ℝ) (ψ : (Fin n → ℝ) → J → ℝ) (x : Fin n → ℝ) :
    6 * kA ψ x ^ 3 * frobT T ≤ wC ℓ H T mu ψ x := by
  have hk : 0 ≤ kA ψ x := Finset.sum_nonneg fun q _ => sq_nonneg _
  have h1 : 0 ≤ nsq (AxC ℓ H T mu ψ x) := Finset.sum_nonneg fun q _ => sq_nonneg _
  have h2 : 0 ≤ frobH (HxC H T mu x) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h3 : 0 ≤ kA ψ x * nsq (AxC ℓ H T mu ψ x) := mul_nonneg hk h1
  have h4 : 0 ≤ 2 * kA ψ x ^ 2 * frobH (HxC H T mu x) := by positivity
  unfold wC
  linarith

end cont

lemma frobT_nonneg {n : ℕ} (T : T3 n) : 0 ≤ frobT T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _

/-! ## The constants -/

lemma kYc_nonneg (Lam g4 η ω ζ cH cT e1 e2 e4 : ℝ) (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2)
    (hg4 : 0 ≤ g4) (hη : 0 < η) (hω : 0 < ω) (hζ : 0 < ζ) :
    0 ≤ kYc Lam g4 η ω ζ cH cT e1 e2 e4 := by
  unfold kYc c3c c1c C3c C1c
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 - Lam := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 < u := by rw [hu]; linarith
  positivity

lemma kEc_nonneg (Lam g4 η ω ζ : ℝ) (hL0 : 0 ≤ Lam) (hg4 : 0 ≤ g4) (hη : 0 < η) (hω : 0 < ω)
    (hζ : 0 < ζ) : 0 ≤ kEc Lam g4 η ω ζ := by
  unfold kEc c4c c2c
  positivity

lemma fin_arith (kY kE e3 Z c3 Lam Mb : ℝ) (hkY : 0 ≤ kY) (hkE : 0 ≤ kE) (hZ : 0 ≤ Z)
    (hc3 : 0 < c3) (hL : Lam ≤ 1 / 2) (hMb0 : 0 ≤ Mb) (hfl : (1 - Lam) * (6 * Z) * c3 ≤ Mb) :
    (kY * Mb + kE * (e3 ^ 2 * Z)) ^ 2 ≤
      (kY + kE * (e3 ^ 2 / (6 * c3 * (1 - Lam)))) ^ 2 * Mb ^ 2 := by
  have h1L : 0 < 1 - Lam := by linarith
  have hd : 0 < 6 * c3 * (1 - Lam) := mul_pos (mul_pos (by norm_num) hc3) h1L
  have hZle : Z ≤ Mb / (6 * c3 * (1 - Lam)) := by
    rw [le_div_iff₀ hd]
    have e : Z * (6 * c3 * (1 - Lam)) = (1 - Lam) * (6 * Z) * c3 := by ring
    linarith
  have h := mul_le_mul_of_nonneg_left hZle (mul_nonneg hkE (sq_nonneg e3))
  have e : kE * e3 ^ 2 * (Mb / (6 * c3 * (1 - Lam))) =
      kE * (e3 ^ 2 / (6 * c3 * (1 - Lam))) * Mb := by ring
  have key : kY * Mb + kE * (e3 ^ 2 * Z) ≤ (kY + kE * (e3 ^ 2 / (6 * c3 * (1 - Lam)))) * Mb := by
    have e' : kE * (e3 ^ 2 * Z) = kE * e3 ^ 2 * Z := by ring
    have e'' : (kY + kE * (e3 ^ 2 / (6 * c3 * (1 - Lam)))) * Mb =
        kY * Mb + kE * (e3 ^ 2 / (6 * c3 * (1 - Lam))) * Mb := by ring
    linarith
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) key 2

end VarM

open VarM

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

/-- **The variance bound in one slice of the model**, with the floor of `Ȳ_p` at level `τ2_p`. -/
theorem cubSliceM (M : Mod n I J S G) (d : ℕ) (Lam g4 K : ℝ) (tau rho tau2 : S → ℝ)
    (hR : Reg M d) (hPF : PolyFacts M d)
    (hSph : ∀ᵐ p ∂M.pi, ∀ᵐ g ∂M.ga, ∑ i, M.X (p, g) i ^ 2 = 1)
    (hD : Decor86 M Lam) (hOp : SliceOpF M Lam tau)
    (hrho : ∀ p, 0 ≤ rho p ∧ rho p ^ 2 = tau p)
    (hK : ∀ᵐ p ∂M.pi, ∀ᵐ g ∂M.ga, kapm M (M.X (p, g)) (M.X (p, g)) ≤ K * tau p)
    (h4 : ∀ (p : S) (c : J → ℝ), ∫ g, (∑ q, c q * M.ps (M.X (p, g)) q) ^ 4 ∂M.ga ≤
      (g4 * (Lam * tau p)) ^ 2 * (∑ q, c q ^ 2) ^ 2)
    (htau2 : (∀ p, 0 ≤ tau2 p) ∧
      ∀ᵐ p ∂M.pi, ∀ᵐ g ∂M.ga, tau2 p ≤ kapm M (M.X (p, g)) (M.X (p, g)))
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2) (hg4 : 0 ≤ g4) (hK0 : 0 ≤ K)
    (hCS : CubSliceA) (hVW : VarWC)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (T : T3 n) (A : I → Fin n → ℝ) (sc : ℝ) (hH : H.IsSymm) (hT : SymT T)
    (hRep : CubRep M P f0 ℓ H T A sc)
    (lam cH cT e1 e2 e4 e0 η ω ζ : ℝ) (hcH : 0 ≤ cH) (hcT : 0 ≤ cT)
    (h48 : 48 * K ^ 2 ≤ cH ^ 4) (h5670 : 5670 * K ^ 4 ≤ cT ^ 4) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (he4 : 0 ≤ e4) (hη : 0 < η) (hω : 0 < ω) (hζ : 0 < ζ)
    (hOsc : SliceOscM M ℓ H T A (lam * sc) tau rho e1 e2 e4 e0) :
    ∀ᵐ p ∂M.pi,
      ∫ W, (Ysl M P lam W p - Ybar M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤
        (kYc Lam g4 η ω ζ cH cT e1 e2 e4 * Ybar M P lam p + kEc Lam g4 η ω ζ * e0) ^ 2 ∧
      (1 - Lam) * (6 * ((lam * sc) ^ 2 * tau2 p) ^ 3 * frobT T) ≤ Ybar M P lam p := by
  have hTm := fun P lam => tameFs M d hR hPF P lam
  obtain ⟨hpi, hga, hX, -, -, -⟩ := hR
  obtain ⟨-, hOp⟩ := hOp
  obtain ⟨htau20, htau2⟩ := htau2
  have hkY := kYc_nonneg Lam g4 η ω ζ cH cT e1 e2 e4 hL0 hL1 hg4 hη hω hζ
  have hkE := kEc_nonneg Lam g4 η ω ζ hL0 hg4 hη hω hζ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = lam * sc := ⟨_, rfl⟩
  rw [← hc] at hOsc ⊢
  filter_upwards [hSph, hK, hOsc, htau2] with p hp hKp hOp' ht2p
  obtain ⟨Abar, Hbar, z, hz, hze, hA4, hH4⟩ := hOp'
  obtain ⟨hτ0, hτk, hτop⟩ := hOp p
  have hbc (j : I) : Continuous fun x => M.b x j := by
    unfold Mod.b; exact MvPolynomial.continuous_eval _
  have hpc (q : J) : Continuous fun x => M.ps x q := by
    unfold Mod.ps; exact MvPolynomial.continuous_eval _
  have hps (x : Fin n → ℝ) (q : J) : psM M c x q = c * M.ps x q := rfl
  have hmu : Continuous (muM M A) :=
    continuous_pi fun i => continuous_finsetSum _ fun j _ => (hbc j).mul continuous_const
  have hψ : Continuous (psM M c) :=
    continuous_pi fun q => continuous_const.mul (hpc q)
  have hXp : Measurable (fun g => M.X (p, g)) := hX.comp measurable_prodMk_left
  obtain ⟨ν, hνd⟩ : ∃ ν : Measure (Fin n → ℝ), ν = Measure.map (fun g => M.X (p, g)) M.ga :=
    ⟨_, rfl⟩
  have hms : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hν : SphLaw n ν := by
    rw [hνd]
    exact ⟨(Measure.isProbabilityMeasure_map_iff hXp.aemeasurable).2 hga,
      (ae_map_iff hXp.aemeasurable hms).2 hp⟩
  have hνp := hν.prob
  have hint (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
      ∫ x, f x ∂ν = ∫ g, f (M.X (p, g)) ∂M.ga := by
    rw [hνd]; exact integral_map hXp.aemeasurable hf.aestronglyMeasurable
  have hFm (W : J × Fin n → ℝ) (x : Fin n → ℝ) :
      Fm M P lam W x = FC f0 ℓ H T (muM M A) (psM M c) W x := by
    rw [hRep]
    unfold FC
    congr 1
    funext i
    have : zv W (psM M c x) i = c * zv W (M.ps x) i := by
      unfold zv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [hps]; ring
    rw [this, hc]
    rfl
  have hY (W : J × Fin n → ℝ) :
      Ysl M P lam W p = YC ν f0 ℓ H T (muM M A) (psM M c) W := by
    have cF := c_FC f0 ℓ H T hmu hψ W
    unfold YC varU
    rw [hint (fun x => (FC f0 ℓ H T (muM M A) (psM M c) W x -
        ∫ y, FC f0 ℓ H T (muM M A) (psM M c) W y ∂ν) ^ 2)
      ((cF.sub continuous_const).pow 2), hint _ cF]
    unfold Ysl msl Fs
    simp only [hFm]
  have hYb : Ybar M P lam p = YbC ν f0 ℓ H T (muM M A) (psM M c) := by
    unfold Ybar YbC
    simp only [hY]
  have hYb0 : 0 ≤ YbC ν f0 ℓ H T (muM M A) (psM M c) := by
    rw [← hYb]; exact Ybar_nonneg M P lam p
  have hkA (x : Fin n → ℝ) : kA (psM M c) x = c ^ 2 * kapm M x x := by
    unfold kA kapm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hps]; ring
  have hk : Continuous (kA (psM M c)) := c_kA hψ
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have ht0 : 0 ≤ c ^ 2 * tau p := mul_nonneg hc2 hτ0
  have hrt0 : 0 ≤ |c| * rho p := mul_nonneg (abs_nonneg c) (hrho p).1
  have hrt2 : (|c| * rho p) ^ 2 = c ^ 2 * tau p := by
    rw [mul_pow, sq_abs, (hrho p).2]
  have hF : FeatOpA ν (psM M c) (Lam * (c ^ 2 * tau p)) := by
    intro cc
    have hcc : Continuous fun x => (∑ q, cc q * psM M c x q) ^ 2 :=
      (continuous_finsetSum _ fun q _ => continuous_const.mul (c_ps hψ q)).pow 2
    rw [hint _ hcc]
    have h := hτop cc
    have e (g : G) : (∑ q, cc q * psM M c (M.X (p, g)) q) ^ 2 =
        c ^ 2 * (∑ q, cc q * M.ps (M.X (p, g)) q) ^ 2 := by
      rw [← mul_pow, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun q _ => by rw [hps]; ring
    simp only [e]
    rw [integral_const_mul]
    calc c ^ 2 * ∫ g, (∑ q, cc q * M.ps (M.X (p, g)) q) ^ 2 ∂M.ga
        ≤ c ^ 2 * (Lam * tau p * ∑ q, cc q ^ 2) := mul_le_mul_of_nonneg_left h hc2
      _ = Lam * (c ^ 2 * tau p) * ∑ q, cc q ^ 2 := by ring
  have hF4 : Feat4A ν (psM M c) (g4 * (Lam * (c ^ 2 * tau p))) := by
    intro cc
    have hcc : Continuous fun x => (∑ q, cc q * psM M c x q) ^ 4 :=
      (continuous_finsetSum _ fun q _ => continuous_const.mul (c_ps hψ q)).pow 4
    rw [hint _ hcc]
    have h := h4 p cc
    have e (g : G) : (∑ q, cc q * psM M c (M.X (p, g)) q) ^ 4 =
        c ^ 4 * (∑ q, cc q * M.ps (M.X (p, g)) q) ^ 4 := by
      rw [← mul_pow, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun q _ => by rw [hps]; ring
    simp only [e]
    rw [integral_const_mul]
    calc c ^ 4 * ∫ g, (∑ q, cc q * M.ps (M.X (p, g)) q) ^ 4 ∂M.ga
        ≤ c ^ 4 * ((g4 * (Lam * tau p)) ^ 2 * (∑ q, cc q ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (g4 * (Lam * (c ^ 2 * tau p))) ^ 2 * (∑ q, cc q ^ 2) ^ 2 := by ring
  have hkk : ∀ᵐ x ∂ν, c ^ 2 * tau p ≤ kA (psM M c) x ∧
      kA (psM M c) x ≤ K * (c ^ 2 * tau p) := by
    have hms2 : MeasurableSet {x : Fin n → ℝ | c ^ 2 * tau p ≤ kA (psM M c) x ∧
        kA (psM M c) x ≤ K * (c ^ 2 * tau p)} :=
      ((isClosed_le continuous_const hk).inter (isClosed_le hk continuous_const)).measurableSet
    rw [hνd]
    refine (ae_map_iff hXp.aemeasurable hms2).2 ?_
    filter_upwards [hτk, hKp] with g hg1 hg2
    rw [hkA]
    refine ⟨mul_le_mul_of_nonneg_left hg1 hc2, ?_⟩
    have := mul_le_mul_of_nonneg_left hg2 hc2
    linarith
  have hkt2 : ∀ᵐ x ∂ν, c ^ 2 * tau2 p ≤ kA (psM M c) x := by
    have hms2 : MeasurableSet {x : Fin n → ℝ | c ^ 2 * tau2 p ≤ kA (psM M c) x} :=
      (isClosed_le continuous_const hk).measurableSet
    rw [hνd]
    refine (ae_map_iff hXp.aemeasurable hms2).2 ?_
    filter_upwards [ht2p] with g hg
    rw [hkA]
    exact mul_le_mul_of_nonneg_left hg hc2
  -- the floor
  have cw := c_wC ℓ H T hmu hψ
  have hL : Lsl M P lam p = ∫ x, wC ℓ H T (muM M A) (psM M c) x ∂ν := by
    rw [hint _ cw]
    unfold Lsl
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have h := (hVW n J f0 ℓ H hH T hT (muM M A) (psM M c) (M.X (p, g))).2.2
    show ∫ W, (Fs M P lam W p g - Phi M P lam (M.X (p, g))) ^ 2 ∂stdGauss (J × Fin n) =
      wC ℓ H T (muM M A) (psM M c) (M.X (p, g))
    rw [← h]
    unfold Fs Phi
    simp only [hFm]
  have h1L : 0 ≤ 1 - Lam := by linarith
  have hfloor : (1 - Lam) * ∫ x, wC ℓ H T (muM M A) (psM M c) x ∂ν ≤
      YbC ν f0 ℓ H T (muM M A) (psM M c) := by
    rw [← hL, ← hYb, Ybar_eq M P lam hTm p]
    have h1 : vsl M P lam p ≤ Lam * Lsl M P lam p := hD P lam p
    have h2 := L_le_q M P lam hTm p
    linarith
  have hA' : ∫ x, (nsq (fun i => AxC ℓ H T (muM M A) (psM M c) x i - Abar i)) ^ 2 ∂ν ≤
      (e1 * (|c| * rho p) * Real.sqrt (frobH Hbar) +
        e2 * (c ^ 2 * tau p) * Real.sqrt (frobT T) + z) ^ 4 := by
    rw [hint _ (c_oscA ℓ H T hmu hψ Abar)]; exact hA4
  have hH' : ∫ x, (frobH (HxC H T (muM M A) x - Hbar)) ^ 2 ∂ν ≤
      (e4 * (|c| * rho p) * Real.sqrt (frobT T)) ^ 4 := by
    rw [hint _ (c_oscH H T hmu Hbar)]; exact hH4
  have hmain := hCS n J ν hν f0 ℓ H hH T hT (muM M A) (psM M c) hmu hψ Lam g4 K
    (c ^ 2 * tau p) (|c| * rho p) cH cT hL0 hL1 hg4 hK0 hrt0 hrt2 hcH hcT h48 h5670 hF hF4 hkk
    hfloor Abar Hbar e1 e2 e4 z he1 he2 he4 hz hA' hH' η ω ζ hη hω hζ
  refine ⟨?_, ?_⟩
  · rw [hYb]
    simp only [hY]
    refine hmain.trans ?_
    have hz2 : 0 ≤ c ^ 2 * tau p * z ^ 2 := mul_nonneg ht0 (sq_nonneg z)
    have h1 := mul_le_mul_of_nonneg_left hze hkE
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  · rw [hYb]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ h1L) hfloor
    have hae : ∀ᵐ x ∂ν, 6 * (c ^ 2 * tau2 p) ^ 3 * frobT T ≤
        wC ℓ H T (muM M A) (psM M c) x := by
      filter_upwards [hkt2] with x hx
      refine le_trans ?_ (wC_ge ℓ H T (muM M A) (psM M c) x)
      have h3 : (c ^ 2 * tau2 p) ^ 3 ≤ kA (psM M c) x ^ 3 :=
        pow_le_pow_left₀ (mul_nonneg hc2 (htau20 p)) hx 3
      have := mul_le_mul_of_nonneg_right h3 (frobT_nonneg T)
      linarith
    have h := integral_mono_ae (integrable_const _) (integrable_cont_sph56 hν cw) hae
    simpa using h

/-- **The variance bound for the within-slice variance of a cubic**. -/
theorem cubVarM {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    [MeasurableSpace G] (M : Mod n I J S G) (d : ℕ) (Lam g4 K : ℝ) (tau rho tau2 : S → ℝ) (c3 : ℝ)
    (hR : Reg M d) (hPF : PolyFacts M d)
    (hSph : ∀ᵐ p ∂M.pi, ∀ᵐ g ∂M.ga, ∑ i, M.X (p, g) i ^ 2 = 1)
    (hD : Decor86 M Lam) (hOp : SliceOpF M Lam tau)
    (hrho : ∀ p, 0 ≤ rho p ∧ rho p ^ 2 = tau p)
    (hK : ∀ᵐ p ∂M.pi, ∀ᵐ g ∂M.ga, kapm M (M.X (p, g)) (M.X (p, g)) ≤ K * tau p)
    (h4 : ∀ (p : S) (c : J → ℝ), ∫ g, (∑ q, c q * M.ps (M.X (p, g)) q) ^ 4 ∂M.ga ≤
      (g4 * (Lam * tau p)) ^ 2 * (∑ q, c q ^ 2) ^ 2)
    (htau2 : Measurable tau2 ∧ (∀ p, 0 ≤ tau2 p) ∧
      ∀ᵐ p ∂M.pi, ∀ᵐ g ∂M.ga, tau2 p ≤ kapm M (M.X (p, g)) (M.X (p, g)))
    (hc3 : 0 < c3) (hc3' : c3 ≤ ∫ p, tau2 p ^ 3 ∂M.pi)
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2) (hg4 : 0 ≤ g4) (hK0 : 0 ≤ K)
    (hCS : CubSliceA) (hVW : VarWC) : CubVarM M Lam g4 K tau rho c3 := by
  intro P f0 ℓ H T A sc hH hT hRep lam cH cT e1 e2 e4 e3 η ω ζ hcH hcT h48 h5670 he1 he2 he4 he3
    hη hω hζ hOsc
  have hsl := cubSliceM M d Lam g4 K tau rho tau2 hR hPF hSph hD hOp hrho hK h4 htau2.2 hL0 hL1
    hg4 hK0 hCS hVW P f0 ℓ H T A sc hH hT hRep lam cH cT e1 e2 e4
    (e3 ^ 2 * ((lam * sc) ^ 2) ^ 3 * frobT T) η ω ζ hcH hcT h48 h5670 he1 he2 he4 hη hω hζ hOsc
  have := hR.1
  have := hR.2.1
  have hTm := fun P lam => tameFs M d hR hPF P lam
  have hkY := kYc_nonneg Lam g4 η ω ζ cH cT e1 e2 e4 hL0 hL1 hg4 hη hω hζ
  have hkE := kEc_nonneg Lam g4 η ω ζ hL0 hg4 hη hω hζ
  obtain ⟨kY, hkYd⟩ : ∃ kY : ℝ, kY = kYc Lam g4 η ω ζ cH cT e1 e2 e4 := ⟨_, rfl⟩
  obtain ⟨kE, hkEd⟩ : ∃ kE : ℝ, kE = kEc Lam g4 η ω ζ := ⟨_, rfl⟩
  obtain ⟨Z, hZd⟩ : ∃ Z : ℝ, Z = ((lam * sc) ^ 2) ^ 3 * frobT T := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZd]; exact mul_nonneg (by positivity) (frobT_nonneg T)
  have he0 : e3 ^ 2 * ((lam * sc) ^ 2) ^ 3 * frobT T = e3 ^ 2 * Z := by rw [hZd]; ring
  rw [he0] at hsl
  rw [← hkYd] at hsl hkY ⊢
  rw [← hkEd] at hsl hkE ⊢
  have h1L : 0 ≤ 1 - Lam := by linarith
  -- tame functions
  have tY := t_Y M P lam hTm
  have tYb : Tame (ι := J × Fin n) (fun _ (p : S) => Ybar M P lam p) := tY.intW
  set s : S → ℝ := fun p => kY * Ybar M P lam p + kE * (e3 ^ 2 * Z) with hs
  have ts : Tame (ι := J × Fin n) (fun _ (p : S) => s p) :=
    ((Tame.const kY).mul tYb).add (Tame.const (kE * (e3 ^ 2 * Z)))
  have hs0 : ∀ p, 0 ≤ s p := fun p => by
    have := Ybar_nonneg M P lam p
    show 0 ≤ kY * Ybar M P lam p + kE * (e3 ^ 2 * Z)
    positivity
  have iYb : Integrable (fun p => Ybar M P lam p) M.pi := tYb.int_par M.pi
  have hVs : ∀ᵐ p ∂M.pi,
      ∫ W, (Ysl M P lam W p - Ybar M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤ s p ^ 2 :=
    hsl.mono fun p hp => hp.1
  -- pairs of slices
  set Mb := ∫ p, Ybar M P lam p ∂M.pi with hMb
  have th : Tame (fun (W : J × Fin n → ℝ) (p : S) => Ysl M P lam W p - Ybar M P lam p) :=
    tY.sub tYb
  have tH : Tame (fun (W : J × Fin n → ℝ) (z : S × S) =>
      (Ysl M P lam W z.1 - Ybar M P lam z.1) * (Ysl M P lam W z.2 - Ybar M P lam z.2)) :=
    (th.comp_right measurable_fst).mul (th.comp_right measurable_snd)
  have e1' : ∀ W, (Vdn M P lam W - Mb) ^ 2 =
      ∫ z, (Ysl M P lam W z.1 - Ybar M P lam z.1) * (Ysl M P lam W z.2 - Ybar M P lam z.2)
        ∂(M.pi.prod M.pi) := by
    intro W
    have a' : Vdn M P lam W - Mb = ∫ p, (Ysl M P lam W p - Ybar M P lam p) ∂M.pi :=
      (integral_sub (tY.int_right W M.pi) iYb).symm
    have b' := integral_prod_mul (μ := M.pi) (ν := M.pi)
      (fun p => Ysl M P lam W p - Ybar M P lam p) (fun p => Ysl M P lam W p - Ybar M P lam p)
    rw [a', sq]; exact b'.symm
  have hpt : ∀ᵐ z ∂(M.pi.prod M.pi),
      ∫ W, (Ysl M P lam W z.1 - Ybar M P lam z.1) * (Ysl M P lam W z.2 - Ybar M P lam z.2)
        ∂stdGauss (J × Fin n) ≤ s z.1 * s z.2 := by
    have g1 : ∀ᵐ z ∂(M.pi.prod M.pi),
        ∫ W, (Ysl M P lam W z.1 - Ybar M P lam z.1) ^ 2 ∂stdGauss (J × Fin n) ≤ s z.1 ^ 2 :=
      (Measure.quasiMeasurePreserving_fst (μ := M.pi) (ν := M.pi)).ae hVs
    have g2 : ∀ᵐ z ∂(M.pi.prod M.pi),
        ∫ W, (Ysl M P lam W z.2 - Ybar M P lam z.2) ^ 2 ∂stdGauss (J × Fin n) ≤ s z.2 ^ 2 :=
      (Measure.quasiMeasurePreserving_snd (μ := M.pi) (ν := M.pi)).ae hVs
    filter_upwards [g1, g2] with z hA hB
    have hcs := cs_sq (stdGauss (J × Fin n))
      (fun W => Ysl M P lam W z.1 - Ybar M P lam z.1)
      (fun W => Ysl M P lam W z.2 - Ybar M P lam z.2)
      ((th.pow 2).int_left z.1) ((th.pow 2).int_left z.2) (tH.int_left z)
    have hX : 0 ≤ s z.1 * s z.2 := mul_nonneg (hs0 _) (hs0 _)
    have hprod := mul_le_mul hA hB (integral_nonneg fun W => sq_nonneg _) (sq_nonneg (s z.1))
    have hsq : (∫ W, (Ysl M P lam W z.1 - Ybar M P lam z.1) *
        (Ysl M P lam W z.2 - Ybar M P lam z.2) ∂stdGauss (J × Fin n)) ^ 2 ≤
        (s z.1 * s z.2) ^ 2 := by
      refine (hcs.trans hprod).trans (le_of_eq ?_); ring
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq hX)
  have iR : Integrable (fun z : S × S => s z.1 * s z.2) (M.pi.prod M.pi) :=
    ((ts.comp_right measurable_fst).mul (ts.comp_right measurable_snd)).int_par (M.pi.prod M.pi)
  have hstep1 : ∫ W, (Vdn M P lam W - Mb) ^ 2 ∂stdGauss (J × Fin n) ≤
      (∫ p, s p ∂M.pi) ^ 2 := by
    simp only [e1']
    rw [tH.swap (M.pi.prod M.pi)]
    have h1 := integral_mono_ae (tH.intW.int_par (M.pi.prod M.pi)) iR hpt
    rw [integral_prod_mul (μ := M.pi) (ν := M.pi) s s] at h1
    rw [sq]; exact h1
  have hsint : ∫ p, s p ∂M.pi = kY * Mb + kE * (e3 ^ 2 * Z) := by
    show ∫ p, (kY * Ybar M P lam p + kE * (e3 ^ 2 * Z)) ∂M.pi = _
    rw [integral_add (iYb.const_mul kY) (integrable_const _), integral_const_mul,
      integral_const]
    simp [hMb]
  have hMb0 : 0 ≤ Mb := integral_nonneg (Ybar_nonneg M P lam)
  -- the global floor
  have hfl : (1 - Lam) * (6 * Z) * c3 ≤ Mb := by
    have hfa : ∀ᵐ p ∂M.pi, (1 - Lam) * (6 * Z) * tau2 p ^ 3 ≤ Ybar M P lam p := by
      filter_upwards [hsl] with p hp
      refine le_trans (le_of_eq ?_) hp.2
      rw [hZd]; ring
    have hnn : 0 ≤ᵐ[M.pi] fun p => (1 - Lam) * (6 * Z) * tau2 p ^ 3 :=
      Filter.Eventually.of_forall fun p => by
        have := htau2.2.1 p
        show (0 : ℝ) ≤ (1 - Lam) * (6 * Z) * tau2 p ^ 3
        positivity
    have h1 := integral_mono_of_nonneg hnn iYb hfa
    rw [integral_const_mul] at h1
    have h2 : (1 - Lam) * (6 * Z) * c3 ≤ (1 - Lam) * (6 * Z) * ∫ p, tau2 p ^ 3 ∂M.pi :=
      mul_le_mul_of_nonneg_left hc3' (by positivity)
    exact h2.trans h1
  rw [hsint] at hstep1
  exact hstep1.trans (fin_arith kY kE e3 Z c3 Lam Mb hkY hkE hZ0 hc3 hL1 hMb0 hfl)

#print axioms cubSliceM
#print axioms cubVarM

end BstLean.Part90
