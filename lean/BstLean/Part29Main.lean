import BstLean.Part29Branches
import BstLean.Part29Bridge
import BstLean.Part29Covariance
import BstLean.Part29Overlap
import BstLean.Part29Normalize
import BstLean.Part29Probability

/-!
# Part 29 in Lean: the accuracy of each branch

`proofs/option-m/29-explicit-22-at-100.tex`. `M` uniform on the coefficient sphere of `CoefIdx n` is
`Z / ‖Z‖` with `Z` standard Gaussian (`stdGauss`). The law of `x` has the uniform-sphere moments
(`SphereMoments`, `SphereParity` with `w = 1/(n(n+2)(n+4)(n+6))`), which Mathlib does not supply and which stay
hypotheses. With `v = ‖F‖_F² > 0` and `q = δ − η'ₙ > 0`:

* the heat program is within `ε · sd` of `B` with probability `≥ 1 − δ` once `ε² ≥ h² = 32 ‖Λ‖² / (n²(n+2)² κₙ q)`;
* the `O(n²)` program likewise once `ε² ≥ u² = 8 s_n / (κₙ q)`.

With `Part29Certificate.lean` (the windows overlap at every `n ≥ 100`) this is part 29's theorem, up to the cost
model and the two moment hypotheses.
-/

namespace BstLean.Part29

open MeasureTheory
open scoped NNReal ENNReal

variable {n : ℕ}

private noncomputable def perm4 (a b c d : Fin 4) (h : Function.Bijective (![a,b,c,d] : Fin 4 → Fin 4)) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective _ h

private lemma perm4_apply (a b c d : Fin 4) (h : Function.Bijective (![a,b,c,d] : Fin 4 → Fin 4))
    (i : Fin 4) : perm4 a b c d h i = ![a,b,c,d] i := rfl

private lemma perm4_univ : (Finset.univ : Finset (Equiv.Perm (Fin 4))) =
    {perm4 0 1 2 3 (by decide),
     perm4 0 1 3 2 (by decide),
     perm4 0 2 1 3 (by decide),
     perm4 0 2 3 1 (by decide),
     perm4 0 3 1 2 (by decide),
     perm4 0 3 2 1 (by decide),
     perm4 1 0 2 3 (by decide),
     perm4 1 0 3 2 (by decide),
     perm4 1 2 0 3 (by decide),
     perm4 1 2 3 0 (by decide),
     perm4 1 3 0 2 (by decide),
     perm4 1 3 2 0 (by decide),
     perm4 2 0 1 3 (by decide),
     perm4 2 0 3 1 (by decide),
     perm4 2 1 0 3 (by decide),
     perm4 2 1 3 0 (by decide),
     perm4 2 3 0 1 (by decide),
     perm4 2 3 1 0 (by decide),
     perm4 3 0 1 2 (by decide),
     perm4 3 0 2 1 (by decide),
     perm4 3 1 0 2 (by decide),
     perm4 3 1 2 0 (by decide),
     perm4 3 2 0 1 (by decide),
     perm4 3 2 1 0 (by decide)} := by
  decide

/-- **`coeffS` is `coefC`** for raw coefficients, `F` symmetric. -/
theorem coeffS_eq_coefC (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) (G : Fin n × Fin n × Fin n → ℝ)
    (S : Finset (Fin n)) (hS : S.card = 4) :
    coeffS F (fun k => symOfRaw (fun i j => G (i, j, k))) (S.orderEmbOfFin hS) = coefC F S hS G := by
  classical
  let e := S.orderEmbOfFin hS
  have hlt (a b : Fin 4) (h : a < b) : e a < e b := e.strictMono h
  have h01 := hlt 0 1 (by decide)
  have h02 := hlt 0 2 (by decide)
  have h03 := hlt 0 3 (by decide)
  have h12 := hlt 1 2 (by decide)
  have h13 := hlt 1 3 (by decide)
  have h23 := hlt 2 3 (by decide)
  have hs (a b : Fin n) (h : a < b) (k : Fin n) :
      symOfRaw (fun i j => G (i,j,k)) a b = G (a,b,k) / 2 ∧
      symOfRaw (fun i j => G (i,j,k)) b a = G (a,b,k) / 2 := by
    simp [symOfRaw, ne_of_lt h, ne_of_gt h, h, not_lt.mpr h.le]
  have hsum (k l : Fin n) :
      (∑ π : Equiv.Perm (Fin 4),
        symOfRaw (fun i j => G (i,j,k)) (e (π 0)) (e (π 1)) *
        symOfRaw (fun i j => G (i,j,l)) (e (π 2)) (e (π 3))) =
      G (e 0,e 1,k) * G (e 2,e 3,l) + G (e 2,e 3,k) * G (e 0,e 1,l) +
      G (e 0,e 2,k) * G (e 1,e 3,l) + G (e 1,e 3,k) * G (e 0,e 2,l) +
      G (e 0,e 3,k) * G (e 1,e 2,l) + G (e 1,e 2,k) * G (e 0,e 3,l) := by
    rw [perm4_univ]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, perm4_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      (hs _ _ h01 _).1, (hs _ _ h01 _).2,
      (hs _ _ h02 _).1, (hs _ _ h02 _).2, (hs _ _ h03 _).1, (hs _ _ h03 _).2,
      (hs _ _ h12 _).1, (hs _ _ h12 _).2, (hs _ _ h13 _).1, (hs _ _ h13 _).2,
      (hs _ _ h23 _).1, (hs _ _ h23 _).2]
    ring
  have swap (a b c d : Fin n) :
      (∑ k, ∑ l, F k l * G (a,b,k) * G (c,d,l)) =
      ∑ k, ∑ l, F k l * G (c,d,k) * G (a,b,l) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hF.apply]
    ring
  change (∑ k, ∑ l, F k l * ∑ π : Equiv.Perm (Fin 4),
    symOfRaw (fun i j => G (i,j,k)) (e (π 0)) (e (π 1)) *
      symOfRaw (fun i j => G (i,j,l)) (e (π 2)) (e (π 3))) = _
  simp_rw [hsum, mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc]
  rw [← swap (e 0) (e 1) (e 2) (e 3), ← swap (e 0) (e 2) (e 1) (e 3),
    ← swap (e 0) (e 3) (e 1) (e 2)]
  unfold coefC bil
  change _ = 2 * ((∑ k, ∑ l, F k l * G (e 0,e 1,k) * G (e 2,e 3,l)) +
    (∑ k, ∑ l, F k l * G (e 0,e 2,k) * G (e 1,e 3,l)) +
    (∑ k, ∑ l, F k l * G (e 0,e 3,k) * G (e 1,e 2,l)))
  ring

/-- `sd(M)² = Var_x f(m_M(x))`. -/
noncomputable def varOf (μ : Measure (Fin n → ℝ)) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) : ℝ :=
  ∫ x, (funF f0 g F (mapM (cOf M) (LOf M) (fun k => symOfRaw (aOf M k)) x) - Bof μ f0 g F M) ^ 2 ∂μ

/-- The unit vector `Z / ‖Z‖`. -/
noncomputable def unitOf (Z : CoefIdx n → ℝ) : CoefIdx n → ℝ := (1 / Real.sqrt (∑ i, Z i ^ 2)) • Z

private lemma sum_sq_pos (Z : CoefIdx n → ℝ) (hZ : Z ≠ 0) : 0 < ∑ i, Z i ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hZ
  have hi' : Z i ≠ 0 := hi
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi')
    (Finset.single_le_sum (fun j _ => sq_nonneg (Z j)) (Finset.mem_univ i))

private lemma unit_sq (Z : CoefIdx n → ℝ) (hZ : Z ≠ 0) : ∑ i, unitOf Z i ^ 2 = 1 := by
  classical
  have hp := sum_sq_pos Z hZ
  simp only [unitOf, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [div_pow, one_pow, Real.sq_sqrt hp.le, div_mul_cancel₀ _ hp.ne']

private lemma normalized_qform (A : Matrix (CoefIdx n) (CoefIdx n) ℝ)
    (Z : CoefIdx n → ℝ) (hZ : Z ≠ 0) :
    qformC A (unitOf Z) - A.trace / Fintype.card (CoefIdx n) =
      qformι (A - (A.trace / Fintype.card (CoefIdx n)) • 1) Z / (∑ i, Z i ^ 2) := by
  classical
  have hp := sum_sq_pos Z hZ
  have hs : Real.sqrt (∑ i, Z i ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hn (z : CoefIdx n → ℝ) : qformι (1 : Matrix (CoefIdx n) (CoefIdx n) ℝ) z = ∑ i, z i ^ 2 := by
    simp [qformι, Matrix.one_apply, pow_two]
  have hsub (a : ℝ) : qformι (A - a • 1) Z = qformC A Z - a * ∑ i, Z i ^ 2 := by
    simp only [qformι, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib]
    change qformC A Z - (∑ i, ∑ j, a * (1 : Matrix (CoefIdx n) (CoefIdx n) ℝ) i j * Z i * Z j) = _
    simp only [mul_assoc, ← Finset.mul_sum]
    simp [Matrix.one_apply, pow_two]
  rw [hsub]
  have hscale : qformC A (unitOf Z) = (1 / Real.sqrt (∑ i, Z i ^ 2)) ^ 2 * qformC A Z := by
    simp only [qformC, unitOf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hscale]
  field_simp
  rw [Real.sq_sqrt hp.le]
  ring

private lemma funF_memLp (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (w : ℝ) (hp : SphereParity n μ w) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (f0 : ℝ) (g : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x => funF f0 g F (mapM c L Q x)) 2 μ := by
  classical
  haveI : ENNReal.HolderTriple 8 8 4 := ⟨by
    change ((8 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((8 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((4 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_add]
    norm_num⟩
  haveI : ENNReal.HolderTriple 4 4 2 := ⟨by
    change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_add]
    norm_num⟩
  have hx (i : Fin n) : MemLp (fun x : Fin n → ℝ => x i) 8 μ := by
    apply (integrable_norm_rpow_iff (measurable_pi_apply i).aestronglyMeasurable (by norm_num : (8 : ℝ≥0∞) ≠ 0)
      (by norm_num : (8 : ℝ≥0∞) ≠ ⊤)).mp
    have hi := hp.integ 8 (by omega) (fun _ => i)
    have habs (a : ℝ) : |a| ^ 8 = a ^ 8 := (show Even (8 : ℕ) by decide).pow_abs a
    simpa [Real.rpow_natCast, habs] using hi
  have hxx (i j : Fin n) : MemLp (fun x : Fin n → ℝ => x i * x j) 4 μ :=
    (hx i).fun_mul (hx j)
  have hm (k : Fin n) : MemLp (fun x => mapM c L Q x k) 4 μ := by
    unfold mapM
    refine ((memLp_const (c k)).add ?_).add ?_
    · exact memLp_finsetSum _ (fun i _ => ((hx i).mono_exponent (by norm_num)).const_mul _)
    · exact memLp_finsetSum _ (fun i _ => memLp_finsetSum _ (fun j _ => by
        simpa only [mul_assoc] using (hxx i j).const_mul (Q k i j)))
  unfold funF
  refine ((memLp_const f0).add ?_).add ?_
  · exact memLp_finsetSum _ (fun k _ => ((hm k).mono_exponent (by norm_num)).const_mul _)
  · exact memLp_finsetSum _ (fun k _ => memLp_finsetSum _ (fun l _ => by
      simpa only [mul_assoc] using ((hm k).fun_mul (hm l) :
        MemLp (fun x => mapM c L Q x k * mapM c L Q x l) 2 μ).const_mul (F k l)))

private noncomputable def floorW (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (n + 2) * (n + 4) * (n + 6))

private noncomputable def floorY (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  floorW n * ∑ S ∈ Finset.univ.powersetCard 4, coefX F S G

private lemma coefC_smul (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (hS : S.card = 4) (G : Fin n × Fin n × Fin n → ℝ) (a : ℝ) :
    coefC F S hS (a • G) = a ^ 2 * coefC F S hS G := by
  classical
  have hb (i j u v : Fin n) : bil F (a • G) i j u v = a ^ 2 * bil F G i j u v := by
    simp only [bil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  simp only [coefC, hb]
  ring

private lemma aOf_smul (a : ℝ) (Z : CoefIdx n → ℝ) :
    (fun p : Fin n × Fin n × Fin n => aOf (a • Z) p.2.2 p.1 p.2.1) =
    a • (fun p : Fin n × Fin n × Fin n => aOf Z p.2.2 p.1 p.2.1) := by
  funext p
  simp only [aOf, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma variance_floor (hn : 100 ≤ n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hp : SphereParity n μ (floorW n))
    (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (Z : CoefIdx n → ℝ) (hZ : Z ≠ 0) :
    floorY F (fun p => aOf Z p.2.2 p.1 p.2.1) / (∑ i, Z i ^ 2) ^ 2 ≤
      varOf μ f0 g F (unitOf Z) := by
  classical
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hw : 0 < floorW n := by unfold floorW; positivity
  have hlp := funF_memLp μ (floorW n) hp (cOf (unitOf Z)) (LOf (unitOf Z))
    (fun k => symOfRaw (aOf (unitOf Z) k)) f0 g F
  have hv := var_ge_parity μ (floorW n) hw hp (cOf (unitOf Z)) (LOf (unitOf Z))
    (fun k => symOfRaw (aOf (unitOf Z) k)) f0 g F
    ((memLp_two_iff_integrable_sq hlp.aestronglyMeasurable).mp hlp) (hlp.integrable (by norm_num))
  change _ ≤ varOf μ f0 g F (unitOf Z) at hv
  convert hv using 1
  have hpZ := sum_sq_pos Z hZ
  have he (S : Finset (Fin n)) (hS : S ∈ Finset.univ.powersetCard 4) :
      (if h : S.card = 4 then coeffS F (fun k => symOfRaw (aOf (unitOf Z) k))
        (S.orderEmbOfFin h) else 0) ^ 2 =
      coefX F S (fun p => aOf Z p.2.2 p.1 p.2.1) / (∑ i, Z i ^ 2) ^ 2 := by
    have hc := (Finset.mem_powersetCard.mp hS).2
    rw [dif_pos hc]
    rw [coeffS_eq_coefC F hF (fun p => aOf (unitOf Z) p.2.2 p.1 p.2.1) S hc]
    change coefC F S hc (fun p => aOf ((1 / Real.sqrt (∑ i, Z i ^ 2)) • Z)
      p.2.2 p.1 p.2.1) ^ 2 = _
    rw [aOf_smul, coefC_smul]
    simp only [coefX, dif_pos hc, mul_pow, div_pow, one_pow, Real.sq_sqrt hpZ.le]
    ring
  rw [Finset.sum_congr rfl he]
  simp only [floorY, ← Finset.sum_div, mul_div_assoc]

private lemma choose_four (hn : 4 ≤ n) : (n.choose 4 : ℝ) =
    (n : ℝ) * (n - 1) * (n - 2) * (n - 3) / 24 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 4
  have h' := congrArg (fun a : ℕ => (a : ℝ)) h
  norm_num [Nat.descFactorial_succ, Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega)] at h'
  linarith

private lemma eta_choose (hn : 4 ≤ n) :
    (16 + 32 / 3 * (n - 4 : ℝ) + 16 / 3 * ((n - 4).choose 2 : ℝ)) / n.choose 4 = eta n := by
  rw [choose_four hn, Nat.cast_choose_two]
  rw [Nat.cast_sub hn]
  unfold eta
  congr 1
  ring

private lemma floor_scale (hn : 4 ≤ n) (v : ℝ) :
    floorW n * ((n.choose 4 : ℝ) * (12 * v) / 2) = kappa n * v / 4 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [choose_four hn]
  unfold floorW kappa
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h4 : (n : ℝ) + 4 ≠ 0 := by positivity
  have h6 : (n : ℝ) + 6 ≠ 0 := by positivity
  field_simp
  ring

private lemma floor_coef_failure (hn : 4 ≤ n) (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.IsSymm) (hv : 0 < frobSq F) :
    coefLaw n {G | floorY F G < kappa n * frobSq F / 4} ≤ ENNReal.ofReal (eta n) := by
  classical
  haveI : IsProbabilityMeasure (coefLaw n) := by unfold coefLaw; infer_instance
  let X : Finset (Fin n) → (Fin n × Fin n × Fin n → ℝ) → ℝ :=
    fun S G => if S.card = 4 then coefX F S G else 12 * frobSq F
  have hX (S : Finset (Fin n)) : Integrable (X S) (coefLaw n) := by
    by_cases hS : S.card = 4
    · simpa [X, hS] using (coefX_integrable F S S).2
    · simp only [X, hS, if_false]; exact integrable_const _
  have hX2 (S T : Finset (Fin n)) :
      Integrable (fun G => X S G * X T G) (coefLaw n) := by
    by_cases hS : S.card = 4 <;> by_cases hT : T.card = 4
    · simpa [X, hS, hT] using (coefX_integrable F S T).1
    · simpa [X, hS, hT] using ((coefX_integrable F S S).2.mul_const (12 * frobSq F))
    · simpa [X, hS, hT] using ((coefX_integrable F T T).2.const_mul (12 * frobSq F))
    · simp only [X, hS, hT, if_false]; exact integrable_const _
  have hm (S : Finset (Fin n)) : ∫ G, X S G ∂coefLaw n = 12 * frobSq F := by
    by_cases hS : S.card = 4
    · simpa [X, hS] using coefX_mean F hF S hS
    · simp [X, hS, coefLaw]
  have hc : ∀ S ∈ Finset.univ.powersetCard 4, ∀ T ∈ Finset.univ.powersetCard 4,
      ∫ G, X S G * X T G ∂coefLaw n - (12 * frobSq F) ^ 2 =
      if (S ∩ T).card = 4 then 288 * frobSq F ^ 2 + 288 * trF4 F
      else if (S ∩ T).card = 3 then 96 * trF4 F
      else if (S ∩ T).card = 2 then 32 * trF4 F else 0 := by
    intro S hS T hT
    have hs := (Finset.mem_powersetCard.mp hS).2
    have ht := (Finset.mem_powersetCard.mp hT).2
    simpa [X, hs, ht] using coefX_cov F hF S T hs ht
  have hf := floor_failure n hn (coefLaw n) X (frobSq F) (trF4 F) hv
    (trF4_bounds F hF).1 (trF4_bounds F hF).2 hX2 hX
    (fun S => (hX S).aemeasurable) hm hc
  have he (G : Fin n × Fin n × Fin n → ℝ) :
      (∑ S ∈ Finset.univ.powersetCard 4, X S G) =
      ∑ S ∈ Finset.univ.powersetCard 4, coefX F S G := by
    apply Finset.sum_congr rfl
    intro S hS
    simp [X, (Finset.mem_powersetCard.mp hS).2]
  simp_rw [he] at hf
  rw [eta_choose hn] at hf
  refine (measure_mono ?_).trans hf
  intro G hG
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hw : 0 < floorW n := by unfold floorW; positivity
  change floorW n * _ < _ at hG
  rw [← floor_scale hn (frobSq F)] at hG
  exact (mul_lt_mul_iff_right₀ hw).mp hG

private abbrev CrossIdx (n : ℕ) := {p : Fin n × Fin n × Fin n // p.1 < p.2.1}

private def crossEmbed (p : CrossIdx n) : CoefIdx n :=
  Sum.inr (Sum.inr ⟨p.val, p.property.le⟩)

private lemma crossEmbed_injective : Function.Injective (crossEmbed (n := n)) := by
  intro p q h
  unfold crossEmbed at h
  apply Subtype.ext
  have hh := Sum.inr.inj (Sum.inr.inj h)
  exact congrArg (fun r : {p : Fin n × Fin n × Fin n // p.1 ≤ p.2.1} => r.val) hh

private noncomputable def crossExtend (z : CrossIdx n → ℝ) : Fin n × Fin n × Fin n → ℝ :=
  fun p => if h : p.1 < p.2.1 then z ⟨p,h⟩ else 0

private lemma floorY_cross (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Fin n × Fin n × Fin n → ℝ) :
    floorY F (crossExtend (G ∘ Subtype.val)) = floorY F G := by
  classical
  unfold floorY
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hc := (Finset.mem_powersetCard.mp hS).2
  let e := S.orderEmbOfFin hc
  have hlt (a b : Fin 4) (h : a < b) : e a < e b := e.strictMono h
  have h01 := hlt 0 1 (by decide)
  have h02 := hlt 0 2 (by decide)
  have h03 := hlt 0 3 (by decide)
  have h12 := hlt 1 2 (by decide)
  have h13 := hlt 1 3 (by decide)
  have h23 := hlt 2 3 (by decide)
  simp only [coefX, dif_pos hc, coefC]
  change (2 * (bil F (crossExtend (G ∘ Subtype.val)) (e 0) (e 1) (e 2) (e 3) +
    bil F (crossExtend (G ∘ Subtype.val)) (e 0) (e 2) (e 1) (e 3) +
    bil F (crossExtend (G ∘ Subtype.val)) (e 0) (e 3) (e 1) (e 2))) ^ 2 = _
  simp only [bil, crossExtend, h01, h02, h03, h12, h13, h23, dif_pos,
    Function.comp_apply]
  rfl

private lemma floorY_measurable (F : Matrix (Fin n) (Fin n) ℝ) : Measurable (floorY F) := by
  classical
  unfold floorY
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro S hS
  unfold coefX
  split_ifs
  · unfold coefC bil
    fun_prop
  · fun_prop

private lemma crossExtend_measurable : Measurable (crossExtend (n := n)) := by
  apply measurable_pi_lambda
  intro p
  unfold crossExtend
  split_ifs <;> fun_prop

private lemma floor_gauss_failure (hn : 4 ≤ n) (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.IsSymm) (hv : 0 < frobSq F) :
    stdGauss (CoefIdx n) {Z | floorY F (fun p => aOf Z p.2.2 p.1 p.2.1) <
      kappa n * frobSq F / 4} ≤ ENNReal.ofReal (eta n) := by
  classical
  let A : Set (CrossIdx n → ℝ) := {z | floorY F (crossExtend z) < kappa n * frobSq F / 4}
  have hA : MeasurableSet A :=
    measurableSet_lt ((floorY_measurable F).comp crossExtend_measurable) measurable_const
  have hr : Measurable (fun Z : CoefIdx n → ℝ => Z ∘ crossEmbed) := by fun_prop
  have hg : Measurable (fun G : Fin n × Fin n × Fin n → ℝ => G ∘
      (Subtype.val : CrossIdx n → Fin n × Fin n × Fin n)) := by fun_prop
  have hl1 := stdGauss_map_restrict (crossEmbed (n := n)) crossEmbed_injective
  have hl2 := stdGauss_map_restrict (Subtype.val : CrossIdx n → Fin n × Fin n × Fin n)
    Subtype.val_injective
  have he1 : (fun Z : CoefIdx n → ℝ => Z ∘ crossEmbed) ⁻¹' A =
      {Z | floorY F (fun p => aOf Z p.2.2 p.1 p.2.1) < kappa n * frobSq F / 4} := by
    ext Z
    have he : ((fun p => aOf Z p.2.2 p.1 p.2.1) ∘
      (Subtype.val : CrossIdx n → Fin n × Fin n × Fin n)) = Z ∘ crossEmbed := by
      funext p
      simp [aOf, crossEmbed, p.property.le]
    simp only [Set.mem_preimage, A, Set.mem_setOf_eq]
    rw [← he, floorY_cross]
  have he2 : (fun G : Fin n × Fin n × Fin n → ℝ => G ∘
      (Subtype.val : CrossIdx n → Fin n × Fin n × Fin n)) ⁻¹' A =
      {G | floorY F G < kappa n * frobSq F / 4} := by
    ext G
    simp only [Set.mem_preimage, A, Set.mem_setOf_eq, floorY_cross]
  rw [← he1, ← Measure.map_apply hr hA, hl1, ← hl2, Measure.map_apply hg hA, he2]
  exact floor_coef_failure hn F hF hv

private lemma branch_bound (hn : 100 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hp : SphereParity n μ (floorW n)) (f0 : ℝ) (g : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) (hv : 0 < frobSq F)
    (A : Matrix (CoefIdx n) (CoefIdx n) ℝ) (hA : A.IsSymm)
    (J : (CoefIdx n → ℝ) → ℝ)
    (hJ : ∀ Z, Z ≠ 0 → Bof μ f0 g F (unitOf Z) - J (unitOf Z) =
      qformC A (unitOf Z) - A.trace / Fintype.card (CoefIdx n))
    (δ ε : ℝ) (hδ : eta n < δ) (hσ : 0 < 2 * ∑ i, ∑ j, A i j ^ 2)
    (hε : (2 * ∑ i, ∑ j, A i j ^ 2) /
      ((δ - eta n) * (kappa n * frobSq F / 4)) ≤ ε ^ 2) :
    stdGauss (CoefIdx n) {Z | Z ≠ 0 ∧ ε ^ 2 * varOf μ f0 g F (unitOf Z) <
      (Bof μ f0 g F (unitOf Z) - J (unitOf Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  classical
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : 4 ≤ n := by omega
  have hk : 0 < kappa n := by
    unfold kappa
    apply div_pos
    · apply mul_pos (mul_pos ?_ ?_) ?_ <;> linarith
    · positivity
  have hy0 : 0 < kappa n * frobSq F / 4 := by positivity
  have heta : 0 ≤ eta n := by
    unfold eta
    apply div_nonneg
    · have h4 : 0 ≤ (n : ℝ) - 4 := by linarith
      have h5 : 0 ≤ (n : ℝ) - 5 := by linarith
      positivity
    · have h1 : 0 ≤ (n : ℝ) - 1 := by linarith
      have h2 : 0 ≤ (n : ℝ) - 2 := by linarith
      have h3 : 0 ≤ (n : ℝ) - 3 := by linarith
      positivity
  have hcard : 0 < Fintype.card (CoefIdx n) := by
    have hc := card_coefIdx n
    have : 0 < n * ((n + 1) * (n + 2)) := by positivity
    omega
  let E : (CoefIdx n → ℝ) → ℝ :=
    qformι (A - (A.trace / Fintype.card (CoefIdx n)) • 1)
  let Y : (CoefIdx n → ℝ) → ℝ := fun Z => floorY F (fun p => aOf Z p.2.2 p.1 p.2.1)
  have hE : Measurable E := by unfold E qformι; fun_prop
  have hE2 := stdGauss_qform_sq_integrable (A - (A.trace / Fintype.card (CoefIdx n)) • 1)
  have hint : ∫ Z, E Z ^ 2 ∂stdGauss (CoefIdx n) ≤ 2 * ∑ i, ∑ j, A i j ^ 2 := by
    exact stdGauss_centred_sq_le hcard A hA
  have hb := chebyshev_floor (stdGauss (CoefIdx n)) E Y hE.aemeasurable hE2
    (2 * ∑ i, ∑ j, A i j ^ 2) (kappa n * frobSq F / 4) (eta n) δ
    hσ heta hδ hint (floor_gauss_failure hn4 F hF hv)
  refine (measure_mono ?_).trans hb
  intro Z hZ hgood
  obtain ⟨hne, hbad⟩ := hZ
  have hd := sum_sq_pos Z hne
  have hd2 := sq_pos_of_pos hd
  have herr : Bof μ f0 g F (unitOf Z) - J (unitOf Z) = E Z / (∑ i, Z i ^ 2) := by
    rw [hJ Z hne, normalized_qform A Z hne]
  have hvar := variance_floor hn μ hp f0 g F hF Z hne
  have hε' : (2 * ∑ i, ∑ j, A i j ^ 2) / (δ - eta n) ≤
      ε ^ 2 * (kappa n * frobSq F / 4) := by
    rw [← div_div] at hε
    exact (div_le_iff₀ hy0).mp hε
  have heY : E Z ^ 2 ≤ ε ^ 2 * Y Z :=
    hgood.2.trans (hε'.trans (mul_le_mul_of_nonneg_left hgood.1 (sq_nonneg ε)))
  have hfin : (Bof μ f0 g F (unitOf Z) - J (unitOf Z)) ^ 2 ≤
      ε ^ 2 * varOf μ f0 g F (unitOf Z) := by
    rw [herr, div_pow]
    calc
      E Z ^ 2 / (∑ i, Z i ^ 2) ^ 2 ≤ (ε ^ 2 * Y Z) / (∑ i, Z i ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right heY hd2.le
      _ = ε ^ 2 * (Y Z / (∑ i, Z i ^ 2) ^ 2) := mul_div_assoc _ _ _
      _ ≤ ε ^ 2 * varOf μ f0 g F (unitOf Z) :=
        mul_le_mul_of_nonneg_left hvar (sq_nonneg ε)
  exact (not_lt_of_ge hfin) hbad

/-- **The heat branch.** -/
theorem heat_branch (hn : 100 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereMoments n μ) (hp : SphereParity n μ (1 / ((n : ℝ) * (n + 2) * (n + 4) * (n + 6))))
    (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) (hv : 0 < frobSq F)
    (δ ε : ℝ) (hδ : eta n < δ)
    (hε : 32 * Lam n / ((n : ℝ) ^ 2 * (n + 2) ^ 2 * kappa n * (δ - eta n)) ≤ ε ^ 2) :
    stdGauss (CoefIdx n) {Z | Z ≠ 0 ∧
      ε ^ 2 * varOf μ f0 g F (unitOf Z) < (Bof μ f0 g F (unitOf Z) - Hof f0 g F (unitOf Z)) ^ 2} ≤
        ENNReal.ofReal δ := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hk : 0 < kappa n := by
    unfold kappa
    apply div_pos
    · apply mul_pos (mul_pos ?_ ?_) ?_ <;> linarith
    · positivity
  have hq : 0 < δ - eta n := sub_pos.mpr hδ
  have hL : 0 < Lam n := by unfold Lam; positivity
  have hf : (2 * ∑ i, ∑ j, AH F i j ^ 2) =
      8 * frobSq F * Lam n / ((n : ℝ) ^ 2 * (n + 2) ^ 2) := by
    rw [AH_frob hn1 F]
    change 2 * (4 * frobSq F * Lam n / _) = _
    ring
  have hσ : 0 < 2 * ∑ i, ∑ j, AH F i j ^ 2 := by rw [hf]; positivity
  have hratio : (2 * ∑ i, ∑ j, AH F i j ^ 2) /
      ((δ - eta n) * (kappa n * frobSq F / 4)) =
      32 * Lam n / ((n : ℝ) ^ 2 * (n + 2) ^ 2 * kappa n * (δ - eta n)) := by
    rw [hf]
    field_simp
    ring
  refine branch_bound hn μ hp f0 g F hF hv (AH F) (AH_isSymm F hF)
    (Hof f0 g F) ?_ δ ε hδ hσ ?_
  · intro Z hZ
    exact heat_centred hn1 μ hμ f0 g F hF (unitOf Z) (unit_sq Z hZ)
  · rw [hratio]
    exact hε

/-- **The `O(n²)` branch.** -/
theorem U2_branch (hn : 100 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereMoments n μ) (hp : SphereParity n μ (1 / ((n : ℝ) * (n + 2) * (n + 4) * (n + 6))))
    (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm) (hv : 0 < frobSq F)
    (δ ε : ℝ) (hδ : eta n < δ)
    (hε : 8 * sN n / (kappa n * (δ - eta n)) ≤ ε ^ 2) :
    stdGauss (CoefIdx n) {Z | Z ≠ 0 ∧
      ε ^ 2 * varOf μ f0 g F (unitOf Z) < (Bof μ f0 g F (unitOf Z) - Uof f0 g F (unitOf Z)) ^ 2} ≤
        ENNReal.ofReal δ := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hk : 0 < kappa n := by
    unfold kappa
    apply div_pos
    · apply mul_pos (mul_pos ?_ ?_) ?_ <;> linarith
    · positivity
  have hq : 0 < δ - eta n := sub_pos.mpr hδ
  have hs : 0 < sN n := by
    unfold sN
    have h1 : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have hf : (2 * ∑ i, ∑ j, AU F i j ^ 2) = 2 * frobSq F * sN n := by
    rw [AU_frob hn1 F]
    unfold frobSq
    ring
  have hσ : 0 < 2 * ∑ i, ∑ j, AU F i j ^ 2 := by rw [hf]; positivity
  have hratio : (2 * ∑ i, ∑ j, AU F i j ^ 2) /
      ((δ - eta n) * (kappa n * frobSq F / 4)) =
      8 * sN n / (kappa n * (δ - eta n)) := by
    rw [hf]
    field_simp
    ring
  refine branch_bound hn μ hp f0 g F hF hv (AU F) (AU_isSymm F hF)
    (Uof f0 g F) ?_ δ ε hδ hσ ?_
  · intro Z hZ
    exact U2_centred hn1 μ hμ f0 g F hF (unitOf Z) (unit_sq Z hZ)
  · rw [hratio]
    exact hε

end BstLean.Part29
