import BstLean.Part43Defs
import BstLean.Part29Sphere
import BstLean.Part36Scale
import BstLean.Part36Index
import BstLean.Part33Moments
import BstLean.Part35Wick
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Part 43, wave 1: Lemma E and Lemma T for every law on the sphere

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the statements.
Do not use `native_decide` or `axiom` anywhere.

Suggested route.
* `errE43`: copy `Part41Error.errE` and replace `uniformSphere n` by `μ`, `HQ` by `HR μ`. The law
  enters only through `A_j = T_j ⊗ G^μ_j` and `tr^l(T_j ⊗ G^μ_j) = tr^l T_j ⊗ H^μ_{j,l}` (an identity
  in `x`, before integration). The rest is harmonic orthogonality on the coefficient sphere, chaos
  orthogonality and independence of `r` and `M`. Integrability: `φ` is bounded on the sphere.
* `errT43`: copy `Part41Error.errT` with `RR μ` and a general `τ ≥ 0`.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}


open BstLean.Part41
variable {μ : Measure (Fin n → ℝ)}

private theorem dimension_pos (hn : 1 ≤ n) : 0 < DD n d := by
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
  unfold DD
  exact_mod_cast Fintype.card_pos

private theorem rho_lower (hn : 1 ≤ n) (s : ℕ) :
    DD n d ^ s ≤ rhoD (DD n d) s := by
  unfold rhoD
  calc
    DD n d ^ s = ∏ _i ∈ Finset.range s, DD n d := by simp
    _ ≤ ∏ i ∈ Finset.range s, (DD n d + 2 * i) := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact (dimension_pos hn).le
      · intro i hi; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith

private theorem rho_pos (hn : 1 ≤ n) (s : ℕ) : 0 < rhoD (DD n d) s :=
  lt_of_lt_of_le (pow_pos (dimension_pos hn) s) (rho_lower hn s)

private theorem kap_bound (hn : 1 ≤ n) (s l : ℕ) :
    (kapQ n d (s + 2 * l) l : ℝ) ^ 2 / rhoD (DD n d) s ≤
      (cQ (s + 2 * l) l : ℝ) ^ 2 / DD n d ^ (s + 2 * l) := by
  have hD := dimension_pos (d := d) hn
  let den : ℝ := ∏ i ∈ Finset.range l, (DD n d + 2 * (s : ℝ) + 2 * i)
  have hden : DD n d ^ l ≤ den := by
    dsimp [den]
    calc
      DD n d ^ l = ∏ _i ∈ Finset.range l, DD n d := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod₀
        · intro i hi; exact hD.le
        · intro i hi
          have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
          have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
          linarith
  have hdenpos : 0 < den := lt_of_lt_of_le (pow_pos hD l) hden
  have hk : (kapQ n d (s + 2 * l) l : ℝ) = (cQ (s + 2 * l) l : ℝ) / den := by
    simp [kapQ, den, DQ, DD, Rat.cast_prod, Rat.cast_div,
      Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
  rw [hk, div_pow, div_div]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hD _)
  calc
    DD n d ^ (s + 2 * l) = (DD n d ^ l) ^ 2 * DD n d ^ s := by
      rw [pow_add, pow_mul]; ring
    _ ≤ den ^ 2 * rhoD (DD n d) s := by
      exact mul_le_mul (pow_le_pow_left₀ (pow_pos hD l).le hden 2)
        (rho_lower hn s) (pow_nonneg hD.le s) (sq_nonneg den)

private theorem level_card (k s : ℕ) (hs : 1 ≤ s) :
    ((Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k)).card ≤ Lk k := by
  have hsub : (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k) ⊆
      Finset.range (Lk k) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
    unfold Lk
    omega
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

private theorem sum_square_bound {ι : Type*} (S : Finset ι) (v : ι → ℝ)
    (k : ℕ) (hcard : S.card ≤ Lk k) :
    (∑ i ∈ S, v i) ^ 2 ≤ Lk k * ∑ i ∈ S, v i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) v
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
    (Finset.sum_nonneg fun i hi => sq_nonneg _))

private theorem sum_cast {ι : Type*} [Fintype ι] {s j : ℕ} (hj : j = s)
    (F : (Fin j → ι) → ℝ) :
    (∑ w : Fin s → ι, F (fun t => w (Fin.cast hj t))) = ∑ w, F w := by
  subst j
  rfl

private theorem W_bound (k s : ℕ) (hs : 1 ≤ s)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (T : Tens n) :
    WfrobSqR μ k s K T ≤ Lk k *
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
        (kapQ n d (s + 2 * l) l : ℝ) ^ 2 * frob (trL l (T (s + 2 * l))) *
          frob (fun w : Fin (s + 2 * l - 2 * l) → Mono n d =>
            (RR μ (K (s + 2 * l) l) l w : ℝ)) := by
  classical
  unfold WfrobSqR
  calc
    _ ≤ ∑ a : Fin s → Fin n, ∑ p : Fin s → Mono n d,
        (Lk k : ℝ) * ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
          ((kapQ n d (s + 2 * l) l : ℝ) *
            trL l (T (s + 2 * l)) (fun t => a ⟨t.1, by have := t.2; omega⟩) *
            (RR μ (K (s + 2 * l) l) l
              (fun t : Fin (s + 2 * l - 2 * l) => p ⟨t.1, by have := t.2; omega⟩) : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum; intro a ha
      apply Finset.sum_le_sum; intro p hp
      exact sum_square_bound _ _ k (level_card k s hs)
    _ = _ := by
      simp_rw [← Finset.mul_sum, mul_pow]
      congr 1
      conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_comm]
      have he : s + 2 * l - 2 * l = s := by omega
      simp only [frob]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      apply congrArg₂ (fun x y : ℝ => x * y)
      · apply congrArg (fun x : ℝ => (kapQ n d (s + 2 * l) l : ℝ) ^ 2 * x)
        exact sum_cast he (fun w => trL l (T (s + 2 * l)) w ^ 2)
      · exact sum_cast he (fun w => (RR μ (K (s + 2 * l) l) l w : ℝ) ^ 2)

private theorem regroup_levels (k : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ s ∈ Finset.Icc 1 k,
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k), F (s + 2 * l) l) =
    ∑ jl ∈ levels k, F jl.1 jl.2 := by
  classical
  calc
    _ = ∑ sl ∈ ((Finset.Icc 1 k) ×ˢ Finset.range (k + 1)).filter
        (fun sl => sl.1 + 2 * sl.2 ≤ k), F (sl.1 + 2 * sl.2) sl.2 := by
      simp [Finset.sum_filter, Finset.sum_product]
    _ = _ := by
      apply Finset.sum_bij (fun sl _ => (sl.1 + 2 * sl.2, sl.2))
      · intro sl hsl
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at hsl
        simp only [levels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range]
        omega
      · intro a ha b hb hab
        have h1 := congrArg Prod.fst hab
        have h2 := congrArg Prod.snd hab
        apply Prod.ext <;> dsimp at * <;> omega
      · intro jl hjl
        simp only [levels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at hjl
        refine ⟨(jl.1 - 2 * jl.2, jl.2), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
            Finset.mem_range]
          omega
        · apply Prod.ext
          · dsimp; omega
          · rfl
      · intro sl hsl; rfl


private theorem product_glue {ι : Type*} (j l : ℕ) (hj : 2 * l ≤ j)
    (c : Fin l → ι) (w : Fin (j - 2 * l) → ι) (f : ι → ℝ) :
    (∏ t : Fin j, f (glue j l c w t)) =
      (∏ t : Fin l, f (c t) ^ 2) * ∏ t, f (w t) := by
  classical
  have he : 2 * l + (j - 2 * l) = j := by omega
  rw [← Fin.prod_congr' (fun t => f (glue j l c w t)) he, Fin.prod_univ_add]
  have hleft : (∏ t : Fin (2 * l), f (glue j l c w
      (Fin.cast he (Fin.castAdd (j - 2 * l) t)))) = ∏ t : Fin l, f (c t) ^ 2 := by
    let e : Fin l × Fin 2 ≃ Fin (2 * l) :=
      finProdFinEquiv.trans (finCongr (Nat.mul_comm l 2))
    rw [← e.prod_comp, Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro a ha
    have ht (b : Fin 2) : glue j l c w (Fin.cast he
        (Fin.castAdd (j - 2 * l) (e (a, b)))) = c a := by
      have hb := b.isLt
      have ha' := a.isLt
      dsimp [e, finProdFinEquiv, glue]
      split_ifs with h
      · congr 1
        apply Fin.ext
        dsimp
        omega
      · omega
    simp only [ht, Fin.prod_const]
  rw [hleft]
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  congr 1
  simp [glue]

private theorem combined_sum {r : ℕ}
    (F : (Fin r → Fin n) → ℝ) (G : (Fin r → Mono n d) → ℝ) :
    (∑ c : Fin r → CoefIdxD n d,
      F (fun t => (c t).2.2) * G (fun t => ⟨(c t).1, (c t).2.1⟩)) =
      (∑ a, F a) * ∑ p, G p := by
  classical
  let e : (Fin r → CoefIdxD n d) ≃ (Fin r → Fin n) × (Fin r → Mono n d) :=
    { toFun := fun c => (fun t => (c t).2.2, fun t => ⟨(c t).1, (c t).2.1⟩)
      invFun := fun ap t => ⟨(ap.2 t).1, ((ap.2 t).2, ap.1 t)⟩
      left_inv := fun c => rfl
      right_inv := fun ap => rfl }
  calc
    _ = ∑ ap : (Fin r → Fin n) × (Fin r → Mono n d), F ap.1 * G ap.2 := by
      exact (e.sum_comp (fun ap => F ap.1 * G ap.2))
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

private theorem gaussian_contraction_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {j : ℕ} (A : (Fin j → ι) → ℝ) :
    Integrable (fun Z => contr A (fun _ => Z)) (stdGauss ι) := by
  unfold contr
  exact integrable_finsetSum _ (fun w hw =>
    (BstLean.Part35.stdGauss_prod_integrable j w).const_mul _)

private theorem gaussian_contraction_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {j q : ℕ} (A : (Fin j → ι) → ℝ) (C : (Fin q → ι) → ℝ) :
    Integrable (fun Z => contr A (fun _ => Z) * contr C (fun _ => Z)) (stdGauss ι) ∧
      (∫ Z, contr A (fun _ => Z) * contr C (fun _ => Z) ∂stdGauss ι) =
        ∑ w : Fin j → ι, ∑ v : Fin q → ι,
          A w * C v * ∏ a : ι, BstLean.Part29.gaussMom
            ((Finset.univ.filter (fun t : Fin j => w t = a)).card +
              (Finset.univ.filter (fun t : Fin q => v t = a)).card) := by
  classical
  have hprod (w : Fin j → ι) (v : Fin q → ι) (Z : ι → ℝ) :
      (∏ t, Z (w t)) * ∏ t, Z (v t) = ∏ t, Z (Fin.append w v t) := by
    simp [Fin.prod_univ_add]
  have hi (w : Fin j → ι) (v : Fin q → ι) :
      Integrable (fun Z => A w * C v * ∏ t, Z (Fin.append w v t)) (stdGauss ι) :=
    (BstLean.Part35.stdGauss_prod_integrable (j + q) (Fin.append w v)).const_mul _
  have hex (Z : ι → ℝ) : contr A (fun _ => Z) * contr C (fun _ => Z) =
      ∑ w, ∑ v, A w * C v * ∏ t, Z (Fin.append w v t) := by
    unfold contr
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro v hv
    rw [← hprod]
    ring
  constructor
  · simpa only [hex] using integrable_finsetSum _ (fun w hw =>
      integrable_finsetSum _ (fun v hv => hi w v))
  · simp_rw [hex]
    rw [integral_finsetSum _ (fun w hw => integrable_finsetSum _ (fun v hv => hi w v))]
    apply Finset.sum_congr rfl
    intro w hw
    rw [integral_finsetSum _ (fun v hv => hi w v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [integral_const_mul, BstLean.Part35.stdGauss_prod_moment]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    congr 1
    simp only [Finset.card_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

private lemma sphere_integrable (hμ : SphLaw n μ)
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

private lemma phi_cont (p : Mono n d) : Continuous (fun x => phiM x p) := by
  unfold phiM BstLean.Part36.monoVal
  exact continuous_multiset_prod p.2.1 (fun a _ => continuous_apply a)

private theorem HR_zero_moment (hμ : SphLaw n μ) {s : ℕ} (w : Fin s → Mono n d) :
    Integrable (fun x => ∏ t, phiM x (w t)) μ ∧
      (∫ x, ∏ t, phiM x (w t) ∂μ) = HR μ 0 w := by
  constructor
  · exact sphere_integrable hμ (continuous_finsetProd _ (fun t _ => phi_cont (w t)))
  · simp [HR]

set_option maxHeartbeats 2000000 in
private theorem trace_HR (hμ : SphLaw n μ) (j l : ℕ) (hj : 2 * l ≤ j)
    (w : Fin (j - 2 * l) → Mono n d) :
    trL l (fun v : Fin j → Mono n d => HR μ 0 v) w = HR μ l w := by
  classical
  have hi (c : Fin l → Mono n d) := (HR_zero_moment hμ (glue j l c w)).1
  simp only [trL, HR, pow_zero, one_mul]
  rw [← integral_finsetSum _ (fun c _ => hi c)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp_rw [product_glue j l hj, ← Finset.sum_mul]
  congr 1
  calc
    (∑ c : Fin l → Mono n d, ∏ t, phiM x (c t) ^ 2) =
        ∏ _t : Fin l, ∑ p : Mono n d, phiM x p ^ 2 := by
      exact (Fintype.prod_sum (fun (_t : Fin l) (p : Mono n d) => phiM x p ^ 2)).symm
    _ = phiSq d x ^ l := by simp [phiSq]

private theorem trace_combined (hn : 1 ≤ n) (hμ : SphLaw n μ) (j l : ℕ) (hj : 2 * l ≤ j)
    (A : (Fin j → Fin n) → ℝ) (w : Fin (j - 2 * l) → CoefIdxD n d) :
    trL l (fun v : Fin j → CoefIdxD n d =>
      A (fun t => (v t).2.2) * HR μ 0 (fun t => ⟨(v t).1, (v t).2.1⟩)) w =
      trL l A (fun t => (w t).2.2) * HR μ l (fun t => ⟨(w t).1, (w t).2.1⟩) := by
  classical
  have h1 (c : Fin l → CoefIdxD n d) :
      (fun t => (glue j l c w t).2.2) =
        glue j l (fun t => (c t).2.2) (fun t => (w t).2.2) := by
    funext t
    by_cases ht : t.1 < 2 * l
    · have hg : glue j l c w t = c ⟨t.1 / 2, by omega⟩ := dite_eq_left ht
      apply Eq.trans (congrArg (fun v : CoefIdxD n d => v.2.2) hg)
      symm
      unfold glue
      exact dite_eq_left ht
    · have hg : glue j l c w t = w ⟨t.1 - 2 * l, by have := t.2; omega⟩ := dite_eq_right ht
      apply Eq.trans (congrArg (fun v : CoefIdxD n d => v.2.2) hg)
      symm
      unfold glue
      exact dite_eq_right ht
  have h2 (c : Fin l → CoefIdxD n d) :
      (fun t => (⟨(glue j l c w t).1, (glue j l c w t).2.1⟩ : Mono n d)) =
        glue j l (fun t => (⟨(c t).1, (c t).2.1⟩ : Mono n d))
          (fun t => (⟨(w t).1, (w t).2.1⟩ : Mono n d)) := by
    funext t
    by_cases ht : t.1 < 2 * l
    · have hg : glue j l c w t = c ⟨t.1 / 2, by omega⟩ := dite_eq_left ht
      apply Eq.trans (congrArg (fun v : CoefIdxD n d => (⟨v.1, v.2.1⟩ : Mono n d)) hg)
      symm
      unfold glue
      exact dite_eq_left ht
    · have hg : glue j l c w t = w ⟨t.1 - 2 * l, by have := t.2; omega⟩ := dite_eq_right ht
      apply Eq.trans (congrArg (fun v : CoefIdxD n d => (⟨v.1, v.2.1⟩ : Mono n d)) hg)
      symm
      unfold glue
      exact dite_eq_right ht
  unfold trL
  simp_rw [h1, h2]
  rw [combined_sum (fun c => A (glue j l c (fun t => (w t).2.2)))
    (fun p => (HR μ 0 (glue j l p (fun t => ⟨(w t).1, (w t).2.1⟩)) : ℝ))]
  congr 1
  have h := trace_HR hμ j l hj (fun t => ⟨(w t).1, (w t).2.1⟩)
  unfold trL at h
  exact_mod_cast h

private theorem contraction_sum {ι κ : Type*} [Fintype ι] [Fintype κ] {s : ℕ}
    (A : (Fin s → ι) → ℝ) (C : ι → κ → ℝ) (v : κ → ℝ) :
    contr A (fun _ a => ∑ p, C a p * v p) =
      ∑ w : Fin s → κ, contr A (fun t a => C a (w t)) * ∏ t, v (w t) := by
  classical
  unfold contr
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem map_as_columns (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (a : Fin n) :
    BstLean.Part36.mapMD M x a = ∑ p : Mono n d, colM M p a * phiM x p := by
  classical
  unfold BstLean.Part36.mapMD
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro β hβ
  simp [BstLean.Part36.coefD, colM, phiM, i.isLt]

private theorem B_expansion (hn : 1 ≤ n) (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (M : CoefIdxD n d → ℝ) :
    BofQ μ k f0 T M = f0 + ∑ j ∈ Finset.Icc 1 k, ∑ w : Fin j → Mono n d,
      (HR μ 0 w : ℝ) * contr (T j) (fun t => colM M (w t)) := by
  classical
  let := hμ.prob
  have hval (x : Fin n → ℝ) : fval k f0 T (BstLean.Part36.mapMD M x) =
      f0 + ∑ j ∈ Finset.Icc 1 k, ∑ w : Fin j → Mono n d,
        contr (T j) (fun t => colM M (w t)) * ∏ t, phiM x (w t) := by
    unfold fval
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hm : BstLean.Part36.mapMD M x = fun a => ∑ p : Mono n d, colM M p a * phiM x p :=
      funext (map_as_columns M x)
    rw [hm]
    exact contraction_sum (T j) (fun a p => colM M p a) (phiM x)
  have hint (j : ℕ) (w : Fin j → Mono n d) :
      Integrable (fun x => contr (T j) (fun t => colM M (w t)) * ∏ t, phiM x (w t))
        (μ) :=
    (HR_zero_moment hμ w).1.const_mul _
  unfold BofQ
  simp_rw [hval]
  rw [integral_add (integrable_const _) (integrable_finsetSum _
    (fun j hj => integrable_finsetSum _ (fun w hw => hint j w))), integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ (fun w hw => hint j w))]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum _ (fun w hw => hint j w)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [integral_const_mul, (HR_zero_moment hμ w).2, mul_comm]

private theorem combined_contraction {j : ℕ} (A : (Fin j → Fin n) → ℝ)
    (M : CoefIdxD n d → ℝ) :
    contr (fun v : Fin j → CoefIdxD n d =>
      A (fun t => (v t).2.2) * (HR μ 0 (fun t => (⟨(v t).1, (v t).2.1⟩ : Mono n d)) : ℝ))
      (fun _ => M) =
    ∑ w : Fin j → Mono n d, (HR μ 0 w : ℝ) * contr A (fun t => colM M (w t)) := by
  classical
  let e : (Fin j → CoefIdxD n d) ≃ (Fin j → Fin n) × (Fin j → Mono n d) :=
    { toFun := fun c => (fun t => (c t).2.2, fun t => ⟨(c t).1, (c t).2.1⟩)
      invFun := fun ap t => ⟨(ap.2 t).1, ((ap.2 t).2, ap.1 t)⟩
      left_inv := fun c => rfl
      right_inv := fun ap => rfl }
  unfold contr
  calc
    _ = ∑ ap : (Fin j → Fin n) × (Fin j → Mono n d),
        A ap.1 * (HR μ 0 ap.2 : ℝ) * ∏ t, colM M (ap.2 t) (ap.1 t) := by
      exact e.sum_comp (fun ap => A ap.1 * (HR μ 0 ap.2 : ℝ) *
        ∏ t, colM M (ap.2 t) (ap.1 t))
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

private theorem B_combined (hn : 1 ≤ n) (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (M : CoefIdxD n d → ℝ) :
    BofQ μ k f0 T M = f0 + ∑ j ∈ Finset.Icc 1 k,
      contr (fun v : Fin j → CoefIdxD n d =>
        T j (fun t => (v t).2.2) *
          (HR μ 0 (fun t => (⟨(v t).1, (v t).2.1⟩ : Mono n d)) : ℝ)) (fun _ => M) := by
  rw [B_expansion hn hμ k f0 T M]
  congr 1
  exact Finset.sum_congr rfl (fun j hj => (combined_contraction (T j) M).symm)

private theorem box_of_square_sum {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∑ i, x i ^ 2 ≤ 1) : x ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1) := by
  classical
  have hi (i : ι) : x i ^ 2 ≤ 1 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hx
  constructor <;> intro i
  · nlinarith [hi i, sq_nonneg (x i + 1)]
  · nlinarith [hi i, sq_nonneg (x i - 1)]

private theorem frob_orthogonal_le {ι : Type*} [Fintype ι] {s : ℕ}
    (A W : (Fin s → ι) → ℝ) (h : ∑ w, A w * (W w - A w) = 0) :
    frob A ≤ frob W := by
  have he : frob W = frob A + frob (fun w => W w - A w) := by
    unfold frob
    calc
      _ = ∑ w, (A w ^ 2 + (W w - A w) ^ 2 + 2 * (A w * (W w - A w))) :=
        Finset.sum_congr rfl (fun w _ => by ring)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h]
        ring
  rw [he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

private theorem unit_in_box (Z : CoefIdxD n d → ℝ) :
    unitOfD Z ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1) := by
  apply box_of_square_sum
  by_cases hZ : Z = 0
  · simp [hZ, unitOfD]
  · exact (BstLean.Part36.unitD_sq Z hZ).le

private theorem continuous_map_joint (a : Fin n) :
    Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      BstLean.Part36.mapMD p.1 p.2 a) := by
  classical
  unfold BstLean.Part36.mapMD
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro β hβ
  apply Continuous.mul
  · unfold BstLean.Part36.coefD
    split_ifs <;> fun_prop
  · unfold BstLean.Part36.monoVal
    exact continuous_multiset_prod β.1 (fun b _ => (continuous_apply b).comp continuous_snd)

private theorem continuous_fval_joint (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      fval k f0 T (BstLean.Part36.mapMD p.1 p.2)) := by
  unfold fval contr
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro w hw
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro t ht
  exact continuous_map_joint (w t)

private theorem continuous_branch (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (f0 : ℝ) (T : Tens n) :
    Continuous (gTCR μ k K f0 T) := by
  unfold gTCR contr colM
  fun_prop

private theorem measurable_unit : Measurable (@unitOfD n d) := by
  unfold unitOfD
  fun_prop

set_option maxHeartbeats 800000 in
private theorem error_integrable (hn : 1 ≤ n) (hμ : SphLaw n μ) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (f0 : ℝ) (T : Tens n) :
    Integrable (fun Z => (BofQ μ k f0 T (unitOfD Z) - gTCR μ k K f0 T (unitOfD Z)) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
  classical
  let := hμ.prob
  let boxM := Set.Icc (fun _ : CoefIdxD n d => (-1 : ℝ)) (fun _ => 1)
  let boxX := Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)
  have hcompact : IsCompact (boxM ×ˢ boxX) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image
    (continuous_fval_joint (d := d) k f0 T).norm.continuousOn
  obtain ⟨G, hG⟩ := (isCompact_Icc : IsCompact boxM).bddAbove_image
    (continuous_branch k K f0 T).norm.continuousOn
  have hB (Z : CoefIdxD n d → ℝ) : ‖BofQ μ k f0 T (unitOfD Z)‖ ≤ max C 0 := by
    unfold BofQ
    have hbound : ∀ᵐ x ∂μ,
        ‖fval k f0 T (BstLean.Part36.mapMD (unitOfD Z) x)‖ ≤ max C 0 := by
      filter_upwards [hμ.sphere] with x hx
      exact (hC (Set.mem_image_of_mem _
        (show (unitOfD Z, x) ∈ boxM ×ˢ boxX from
          ⟨unit_in_box Z, box_of_square_sum x hx.le⟩))).trans (le_max_left C 0)
    simpa using norm_integral_le_of_norm_le_const hbound
  have hg (Z : CoefIdxD n d → ℝ) : ‖gTCR μ k K f0 T (unitOfD Z)‖ ≤ max G 0 :=
    (hG (Set.mem_image_of_mem _ (unit_in_box Z))).trans (le_max_left G 0)
  have hmB : Measurable (BofQ μ (d := d) k f0 T) :=
    (continuous_fval_joint k f0 T).measurable.stronglyMeasurable.integral_prod_right'.measurable
  have hm : Measurable (fun Z =>
      (BofQ μ k f0 T (unitOfD Z) - gTCR μ k K f0 T (unitOfD Z)) ^ 2) :=
    ((hmB.comp measurable_unit).sub
      ((continuous_branch k K f0 T).measurable.comp measurable_unit)).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable ((max C 0 + max G 0) ^ 2)
  apply ae_of_all
  intro Z
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
    (add_le_add (hB Z) (hg Z))) 2

private lemma cQ_step (s i : ℕ) (hi : 2 * (i + 1) ≤ s) :
    (2 * (i + 1) : ℚ) * cQ s (i + 1) =
      ((s - 2 * i : ℕ) : ℚ) * ((s - 2 * i - 1 : ℕ) : ℚ) * cQ s i := by
  have h1 : s - 2 * i = (s - 2 * (i + 1)) + 2 := by omega
  have h2 : s - 2 * i - 1 = (s - 2 * (i + 1)) + 1 := by omega
  unfold cQ
  rw [h2, h1, Nat.factorial_succ i, pow_succ,
    show (s - 2 * (i + 1) + 2).factorial =
      (s - 2 * (i + 1) + 2) * (s - 2 * (i + 1) + 1) *
        (s - 2 * (i + 1)).factorial by
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
  have hfi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hfs : ((s - 2 * (i + 1)).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hp : (2 : ℚ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha : ((s - 2 * (i + 1) : ℕ) : ℚ) + 1 ≠ 0 := by positivity
  have hb : ((s - 2 * (i + 1) : ℕ) : ℚ) + 2 ≠ 0 := by positivity
  have hc : (i + 1 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

private lemma muQ_den_pos (hn : 1 ≤ n) (s i : ℕ) (hi : 2 * i ≤ s) :
    0 < ∏ m ∈ Finset.Icc 1 i, (DQ n d + 2 * (s : ℚ) - 2 - 2 * m) := by
  have hD : 0 < DQ n d := by
    have h := dimension_pos (d := d) hn
    unfold DQ
    unfold DD at h
    exact_mod_cast h
  apply Finset.prod_pos
  intro m hm
  obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
  have hsm : 2 + 2 * m ≤ 2 * s := by omega
  have hsmQ : (2 : ℚ) + 2 * m ≤ 2 * s := by exact_mod_cast hsm
  linarith

private lemma muQ_step (hn : 1 ≤ n) (s i : ℕ) (hi : 2 * (i + 1) ≤ s) :
    (2 * (i + 1) : ℚ) * (DQ n d + 2 * s - 4 - 2 * i) * muQ n d s (i + 1) =
      -((s - 2 * i : ℕ) : ℚ) * ((s - 2 * i - 1 : ℕ) : ℚ) * muQ n d s i := by
  have hprod : (∏ m ∈ Finset.Icc 1 (i + 1),
      (DQ n d + 2 * (s : ℚ) - 2 - 2 * m)) =
      (∏ m ∈ Finset.Icc 1 i, (DQ n d + 2 * (s : ℚ) - 2 - 2 * m)) *
        (DQ n d + 2 * s - 4 - 2 * i) := by
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ i + 1)]
    push_cast
    ring
  have hp := (muQ_den_pos (d := d) hn s i (by omega)).ne'
  have hpn := (muQ_den_pos (d := d) hn s (i + 1) hi).ne'
  rw [hprod] at hpn
  have hf := (mul_ne_zero_iff.mp hpn).2
  have hc := cQ_step s i hi
  unfold muQ
  rw [hprod, pow_succ]
  field_simp
  linear_combination -hc

/-! Gaussian Wick lemmas adapted from the proved private lemmas in `Part41Contam.lean`. -/

private lemma gaussian_eval_integrable {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finsetSum
  intro e he
  have hprod (z : ι → ℝ) : e.prod (fun i a => z i ^ a) = ∏ i, z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  exact (Integrable.fintype_prod (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (by simp) (e i))).const_mul _

private lemma gaussMom_step (a : ℕ) :
    BstLean.Part29.gaussMom (a + 2) = (a + 1 : ℝ) * BstLean.Part29.gaussMom a := by
  unfold BstLean.Part29.gaussMom
  have h : Even (a + 2) ↔ Even a := by simp [Nat.even_add]
  simp only [h]
  split_ifs with ha
  · rw [show a + 2 - 1 = a + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl
  · ring

private lemma gaussMom_stein (a : ℕ) :
    BstLean.Part29.gaussMom (a + 1) = (a : ℝ) * BstLean.Part29.gaussMom (a - 1) := by
  cases a with
  | zero => norm_num [BstLean.Part29.gaussMom]
  | succ a => simpa [Nat.succ_eq_add_one] using gaussMom_step a

private lemma gaussian_power_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (i : ι) :
    (∫ Z, Z i * ∏ j, Z j ^ a j ∂stdGauss ι) =
      (a i : ℝ) * ∫ Z, ∏ j, Z j ^ (a j - if j = i then 1 else 0) ∂stdGauss ι := by
  classical
  have he (Z : ι → ℝ) : Z i * (∏ j, Z j ^ a j) =
      ∏ j, Z j ^ (a j + if j = i then 1 else 0) := by
    simp only [pow_add, Finset.prod_mul_distrib]
    simp [mul_comm, Finset.prod_ite_eq']
  simp_rw [he]
  have hmom (b : ι → ℕ) :
      (∫ Z, ∏ j, Z j ^ b j ∂stdGauss ι) = ∏ j, BstLean.Part29.gaussMom (b j) := by
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (f := fun j (x : ℝ) => x ^ b j)]
    simp_rw [BstLean.Part29.gaussMom_eq]
  rw [hmom, hmom, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true, gaussMom_stein]
  have hprod :
      (∏ j ∈ Finset.univ.erase i,
        BstLean.Part29.gaussMom (a j + if j = i then 1 else 0)) =
      ∏ j ∈ Finset.univ.erase i,
        BstLean.Part29.gaussMom (a j - if j = i then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  rw [hprod]
  ring

private lemma gaussian_polynomial_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (i : ι) :
    (∫ Z, Z i * MvPolynomial.eval Z p ∂stdGauss ι) =
      ∫ Z, MvPolynomial.eval Z (MvPolynomial.pderiv i p) ∂stdGauss ι := by
  classical
  have hmono (e : ι →₀ ℕ) (c : ℝ) :
      (∫ Z, Z i * MvPolynomial.eval Z (MvPolynomial.monomial e c) ∂stdGauss ι) =
        ∫ Z, MvPolynomial.eval Z (MvPolynomial.pderiv i (MvPolynomial.monomial e c))
          ∂stdGauss ι := by
    have he (e : ι →₀ ℕ) (Z : ι → ℝ) :
        e.prod (fun j a => Z j ^ a) = ∏ j, Z j ^ e j :=
      Finsupp.prod_fintype _ _ (by simp)
    simp only [MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial, he,
      Finsupp.tsub_apply, Finsupp.single_apply]
    simp_rw [show ∀ Z : ι → ℝ, Z i * (c * ∏ j, Z j ^ e j) =
      c * (Z i * ∏ j, Z j ^ e j) by intro Z; ring]
    rw [integral_const_mul, gaussian_power_stein, integral_const_mul]
    simp only [eq_comm, mul_assoc]
  have hi (q : MvPolynomial ι ℝ) :
      Integrable (fun Z => Z i * MvPolynomial.eval Z q) (stdGauss ι) := by
    have hh := gaussian_eval_integrable (MvPolynomial.X i * q)
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hh
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun e _ => hi _),
    integral_finsetSum _ (fun e _ => gaussian_eval_integrable _)]
  exact Finset.sum_congr rfl (fun e _ => hmono e (p.coeff e))

private noncomputable def gaussianExpectation {ι : Type*} [Fintype ι] :
    MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ Z, MvPolynomial.eval Z p ∂stdGauss ι
  map_add' p q := by
    simp only [MvPolynomial.eval_add]
    exact integral_add (gaussian_eval_integrable p) (gaussian_eval_integrable q)
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, smul_eq_mul]
    exact integral_const_mul _ _

private lemma gaussianExpectation_X_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : MvPolynomial ι ℝ) :
    gaussianExpectation (MvPolynomial.X i * p) =
      gaussianExpectation (MvPolynomial.pderiv i p) := by
  simpa only [gaussianExpectation, LinearMap.coe_mk, AddHom.coe_mk,
    MvPolynomial.eval_mul, MvPolynomial.eval_X] using gaussian_polynomial_stein p i

private noncomputable def wickRaise {ι : Type*} [DecidableEq ι]
    (i : ι) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  MvPolynomial.X i * p - MvPolynomial.pderiv i p

private lemma wickRaise_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p q : MvPolynomial ι ℝ) :
    gaussianExpectation (wickRaise i p * q) =
      gaussianExpectation (p * MvPolynomial.pderiv i q) := by
  have h := gaussianExpectation_X_mul i (p * q)
  rw [MvPolynomial.pderiv_mul, map_add] at h
  unfold wickRaise
  rw [sub_mul, map_sub, mul_assoc, h]
  ring

private noncomputable def wickWord {ι : Type*} [DecidableEq ι] :
    List ι → MvPolynomial ι ℝ
  | [] => 1
  | i :: w => wickRaise i (wickWord w)

private noncomputable def wordDeriv {ι : Type*} [DecidableEq ι] :
    List ι → MvPolynomial ι ℝ → MvPolynomial ι ℝ
  | [], p => p
  | i :: w, p => wordDeriv w (MvPolynomial.pderiv i p)

private lemma wickWord_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) :
    gaussianExpectation (wickWord w * p) = gaussianExpectation (wordDeriv w p) := by
  induction w generalizing p with
  | nil => simp [wickWord, wordDeriv]
  | cons i w ih =>
    rw [wickWord, wickRaise_adjoint, ih]
    rfl

private lemma pderiv_degree {ι : Type*} [DecidableEq ι]
    (i : ι) (p : MvPolynomial ι ℝ) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro e he
  have hc : p.coeff (e + Finsupp.single i 1) ≠ 0 := by
    have hh := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv] at hh
    exact (mul_ne_zero_iff.mp hh).1
  have hh := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  have hs : (e + Finsupp.single i 1).sum (fun _ a => a) = e.sum (fun _ a => a) + 1 := by
    simp [Finsupp.sum_add_index']
  rw [hs] at hh
  exact Nat.le_sub_one_of_lt hh

private lemma wordDeriv_zero {ι : Type*} [DecidableEq ι] (w : List ι) :
    wordDeriv w (0 : MvPolynomial ι ℝ) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa [wordDeriv] using ih

private lemma wordDeriv_eq_zero_of_degree_lt {ι : Type*} [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) (hp : p.totalDegree < w.length) :
    wordDeriv w p = 0 := by
  induction w generalizing p with
  | nil => simp at hp
  | cons i w ih =>
    change wordDeriv w (MvPolynomial.pderiv i p) = 0
    by_cases hz : p.totalDegree = 0
    · have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
      rw [hc, MvPolynomial.pderiv_C]
      exact wordDeriv_zero w
    · apply ih
      have hd := pderiv_degree i p
      simp only [List.length_cons] at hp
      omega

private lemma wickWord_degree {ι : Type*} [DecidableEq ι] (w : List ι) :
    (wickWord w).totalDegree ≤ w.length := by
  induction w with
  | nil => simp [wickWord]
  | cons i w ih =>
    unfold wickWord wickRaise
    have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X i) (wickWord w)
    have hd := pderiv_degree i (wickWord w)
    have hs := MvPolynomial.totalDegree_sub
      (MvPolynomial.X i * wickWord w) (MvPolynomial.pderiv i (wickWord w))
    simp only [MvPolynomial.totalDegree_X] at hm
    simp only [List.length_cons]
    omega

private lemma wickWord_orthogonal_low_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) (hp : p.totalDegree < w.length) :
    gaussianExpectation (wickWord w * p) = 0 := by
  rw [wickWord_adjoint, wordDeriv_eq_zero_of_degree_lt w p hp, map_zero]

private lemma wickWord_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : List ι) (h : w.length ≠ v.length) :
    gaussianExpectation (wickWord w * wickWord v) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [mul_comm]
    exact wickWord_orthogonal_low_degree v (wickWord w) ((wickWord_degree w).trans_lt hlt)
  · exact wickWord_orthogonal_low_degree w (wickWord v) ((wickWord_degree v).trans_lt hgt)

private noncomputable def plainWord {ι : Type*} : List ι → MvPolynomial ι ℝ
  | [] => 1
  | i :: w => MvPolynomial.X i * plainWord w

private lemma wickWord_remainder_degree {ι : Type*} [DecidableEq ι] (w : List ι) :
    (plainWord w - wickWord w).totalDegree ≤ w.length - 1 := by
  induction w with
  | nil => simp [plainWord, wickWord]
  | cons i w ih =>
    cases w with
    | nil => simp [plainWord, wickWord, wickRaise]
    | cons j w =>
      have he : plainWord (i :: j :: w) - wickWord (i :: j :: w) =
          MvPolynomial.X i * (plainWord (j :: w) - wickWord (j :: w)) +
            MvPolynomial.pderiv i (wickWord (j :: w)) := by
        simp only [plainWord, wickWord, wickRaise]
        ring
      rw [he]
      have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X i)
        (plainWord (j :: w) - wickWord (j :: w))
      have hd := pderiv_degree i (wickWord (j :: w))
      have hw := wickWord_degree (j :: w)
      have ha := MvPolynomial.totalDegree_add
        (MvPolynomial.X i * (plainWord (j :: w) - wickWord (j :: w)))
        (MvPolynomial.pderiv i (wickWord (j :: w)))
      simp only [MvPolynomial.totalDegree_X, List.length_cons] at *
      omega

private lemma wickWord_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : List ι) (h : w.length = v.length) :
    gaussianExpectation (wickWord w * wickWord v) =
      gaussianExpectation (wordDeriv w (plainWord v)) := by
  by_cases hv : v = []
  · subst v
    have hw : w = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst w
    simp [plainWord, wickWord, wordDeriv]
  · have hd := wickWord_remainder_degree v
    have hz := wickWord_orthogonal_low_degree w (plainWord v - wickWord v)
      (by have hl := List.length_pos_iff.mpr hv; omega)
    rw [mul_sub, map_sub] at hz
    rw [← wickWord_adjoint]
    linarith

private lemma coeff_nonneg_plainWord {ι : Type*} [DecidableEq ι]
    (w : List ι) (e : ι →₀ ℕ) : 0 ≤ (plainWord w).coeff e := by
  induction w generalizing e with
  | nil => simp only [plainWord, MvPolynomial.coeff_one]; split_ifs <;> norm_num
  | cons i w ih =>
    rw [plainWord, MvPolynomial.coeff_mul]
    apply Finset.sum_nonneg
    intro a ha
    apply mul_nonneg _ (ih a.2)
    simp only [MvPolynomial.coeff_X]
    split_ifs <;> norm_num

private lemma coeff_nonneg_wordDeriv {ι : Type*} [DecidableEq ι]
    (w : List ι) (p : MvPolynomial ι ℝ) (hp : ∀ e, 0 ≤ p.coeff e) :
    ∀ e, 0 ≤ (wordDeriv w p).coeff e := by
  induction w generalizing p with
  | nil => exact hp
  | cons i w ih =>
    apply ih
    intro e
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hp _) (by positivity)

private lemma gaussianExpectation_nonneg_coeff {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (hp : ∀ e, 0 ≤ p.coeff e) :
    0 ≤ gaussianExpectation p := by
  classical
  change 0 ≤ ∫ Z, MvPolynomial.eval Z p ∂stdGauss ι
  conv_rhs => rw [p.as_sum]
  simp only [map_sum]
  rw [integral_finsetSum _ (fun e _ => gaussian_eval_integrable _)]
  apply Finset.sum_nonneg
  intro e he
  simp only [MvPolynomial.eval_monomial]
  have hprod (Z : ι → ℝ) : e.prod (fun i a => Z i ^ a) = ∏ i, Z i ^ e i :=
    Finsupp.prod_fintype _ _ (by simp)
  simp_rw [hprod]
  rw [integral_const_mul]
  apply mul_nonneg (hp _)
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => x ^ e i)]
  simp_rw [BstLean.Part29.gaussMom_eq]
  apply Finset.prod_nonneg
  intro i hi
  unfold BstLean.Part29.gaussMom
  split_ifs <;> positivity

private lemma wickWord_covariance_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : List ι) : 0 ≤ gaussianExpectation (wickWord w * wickWord v) := by
  by_cases h : w.length = v.length
  · rw [wickWord_covariance w v h]
    exact gaussianExpectation_nonneg_coeff _
      (coeff_nonneg_wordDeriv w (plainWord v) (coeff_nonneg_plainWord v))
  · rw [wickWord_orthogonal w v h]

private lemma wordDeriv_sum {ι κ : Type*} [DecidableEq ι]
    (w : List ι) (s : Finset κ) (p : κ → MvPolynomial ι ℝ) :
    wordDeriv w (∑ a ∈ s, p a) = ∑ a ∈ s, wordDeriv w (p a) := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => simp only [wordDeriv, map_sum, ih]

private lemma wordDeriv_C_mul {ι : Type*} [DecidableEq ι]
    (w : List ι) (c : ℝ) (p : MvPolynomial ι ℝ) :
    wordDeriv w (MvPolynomial.C c * p) = MvPolynomial.C c * wordDeriv w p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => simp only [wordDeriv, MvPolynomial.pderiv_C_mul, ih]

private lemma plainWord_ofFn {ι : Type*} {m : ℕ} (w : Fin m → ι) :
    plainWord (List.ofFn w) = ∏ t, (MvPolynomial.X (w t) : MvPolynomial ι ℝ) := by
  induction m with
  | zero => simp [plainWord]
  | succ m ih => simp [List.ofFn_succ, plainWord, Fin.prod_univ_succ, ih]

private lemma wordDeriv_sumX_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (w : List ι) :
    wordDeriv w ((∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℝ)) ^ w.length) =
      MvPolynomial.C (w.length.factorial : ℝ) := by
  induction w with
  | nil => simp [wordDeriv]
  | cons i w ih =>
    have hs : MvPolynomial.pderiv i (∑ j : ι, (MvPolynomial.X j : MvPolynomial ι ℝ)) = 1 := by
      simp [Pi.single_apply]
    simp only [wordDeriv, List.length_cons, MvPolynomial.pderiv_pow, hs,
      Nat.add_sub_cancel, mul_one]
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ)]
    change wordDeriv w (MvPolynomial.C ((w.length + 1 : ℕ) : ℝ) *
      (∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℝ)) ^ w.length) = _
    rw [wordDeriv_C_mul, ih, ← map_mul]
    simp [Nat.factorial_succ, Nat.cast_mul]

private lemma gaussianExpectation_C {ι : Type*} [Fintype ι] (c : ℝ) :
    gaussianExpectation (MvPolynomial.C c : MvPolynomial ι ℝ) = c := by
  simp [gaussianExpectation]

private lemma gaussianExpectation_C_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (p : MvPolynomial ι ℝ) :
    gaussianExpectation (MvPolynomial.C c * p) = c * gaussianExpectation p := by
  simpa only [MvPolynomial.smul_eq_C_mul, smul_eq_mul] using
    (gaussianExpectation (ι := ι)).map_smul c p

private lemma wickWord_covariance_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (w : Fin m → ι) :
    (∑ v : Fin m → ι, gaussianExpectation (wickWord (List.ofFn w) * wickWord (List.ofFn v))) =
      (m.factorial : ℝ) := by
  classical
  have hc (v : Fin m → ι) := wickWord_covariance (List.ofFn w) (List.ofFn v)
    (by simp only [List.length_ofFn])
  simp_rw [hc]
  rw [← map_sum, ← wordDeriv_sum]
  simp_rw [plainWord_ofFn]
  rw [← Fintype.sum_pow]
  have ht := wordDeriv_sumX_pow (List.ofFn w)
  simp only [List.length_ofFn] at ht
  rw [ht, gaussianExpectation_C]

private lemma wickTensor_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (A : (Fin m → ι) → ℝ) :
    gaussianExpectation
      ((∑ w : Fin m → ι, MvPolynomial.C (A w) * wickWord (List.ofFn w)) ^ 2) ≤
      (m.factorial : ℝ) * ∑ w, A w ^ 2 := by
  classical
  let C (w v : Fin m → ι) :=
    gaussianExpectation (wickWord (List.ofFn w) * wickWord (List.ofFn v))
  have hC (w v : Fin m → ι) : 0 ≤ C w v := wickWord_covariance_nonneg _ _
  have hrow (w : Fin m → ι) : ∑ v, C w v = (m.factorial : ℝ) := wickWord_covariance_row w
  have hsym (w v : Fin m → ι) : C w v = C v w := by dsimp [C]; rw [mul_comm]
  have hcol (v : Fin m → ι) : ∑ w, C w v = (m.factorial : ℝ) := by
    simp_rw [hsym]; exact hrow v
  have hex : gaussianExpectation
      ((∑ w : Fin m → ι, MvPolynomial.C (A w) * wickWord (List.ofFn w)) ^ 2) =
      ∑ w, ∑ v, A w * A v * C w v := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro v hv
    have he : (MvPolynomial.C (A w) * wickWord (List.ofFn w)) *
        (MvPolynomial.C (A v) * wickWord (List.ofFn v)) =
        MvPolynomial.C (A w * A v) * (wickWord (List.ofFn w) * wickWord (List.ofFn v)) := by
      rw [map_mul]
      ring
    rw [mul_comm, he, gaussianExpectation_C_mul]
  rw [hex]
  calc
    _ ≤ ∑ w, ∑ v, ((A w ^ 2 + A v ^ 2) / 2) * C w v := by
      apply Finset.sum_le_sum
      intro w hw
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (A w - A v)]) (hC w v)
    _ = (∑ w, ∑ v, (A w ^ 2 * C w v + A v ^ 2 * C w v)) / 2 := by
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = ((∑ w, A w ^ 2 * (m.factorial : ℝ)) +
        ∑ v, A v ^ 2 * (m.factorial : ℝ)) / 2 := by
      simp only [Finset.sum_add_distrib]
      congr 1
      congr 1
      · simp_rw [← Finset.mul_sum, hrow]
      · rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hcol]
    _ = _ := by rw [← Finset.sum_mul]; ring

private noncomputable def wickTensor {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : (Fin m → ι) → ℝ) : MvPolynomial ι ℝ :=
  ∑ w : Fin m → ι, MvPolynomial.C (A w) * wickWord (List.ofFn w)

private lemma wickTensor_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m r : ℕ} (A : (Fin m → ι) → ℝ) (B : (Fin r → ι) → ℝ) (h : m ≠ r) :
    gaussianExpectation (wickTensor A * wickTensor B) = 0 := by
  classical
  unfold wickTensor
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro w hw
  have he : (MvPolynomial.C (A w) * wickWord (List.ofFn w)) *
      (MvPolynomial.C (B v) * wickWord (List.ofFn v)) =
      MvPolynomial.C (A w * B v) * (wickWord (List.ofFn w) * wickWord (List.ofFn v)) := by
    rw [map_mul]
    ring
  rw [he, gaussianExpectation_C_mul,
    wickWord_orthogonal _ _ (by simpa only [List.length_ofFn] using h), mul_zero]

set_option maxHeartbeats 1000000 in
private lemma wickTensor_sum_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ℕ) (A : (m : ℕ) → (Fin m → ι) → ℝ) :
    gaussianExpectation ((∑ m ∈ s, wickTensor (A m)) ^ 2) ≤
      ∑ m ∈ s, (m.factorial : ℝ) * frob (A m) := by
  classical
  have he : gaussianExpectation ((∑ m ∈ s, wickTensor (A m)) ^ 2) =
      ∑ m ∈ s, gaussianExpectation (wickTensor (A m) ^ 2) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_eq_single m
    · intro r hr hrm
      exact wickTensor_orthogonal (A r) (A m) hrm
    · intro hn
      exact (hn hm).elim
  rw [he]
  exact Finset.sum_le_sum (fun m hm => wickTensor_sq_le (A m))

private lemma wickTensor_eval {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : (Fin m → ι) → ℝ) (Z : ι → ℝ) :
    MvPolynomial.eval Z (wickTensor A) =
      ∑ w : Fin m → ι, A w * MvPolynomial.eval Z (wickWord (List.ofFn w)) := by
  simp only [wickTensor, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]

private lemma wick_expansion_l2_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ℕ) (A : (m : ℕ) → (Fin m → ι) → ℝ) :
    Integrable (fun Z => (∑ m ∈ s, ∑ w : Fin m → ι,
      A m w * MvPolynomial.eval Z (wickWord (List.ofFn w))) ^ 2) (stdGauss ι) ∧
    (∫ Z, (∑ m ∈ s, ∑ w : Fin m → ι,
      A m w * MvPolynomial.eval Z (wickWord (List.ofFn w))) ^ 2 ∂stdGauss ι) ≤
      ∑ m ∈ s, (m.factorial : ℝ) * frob (A m) := by
  have he (Z : ι → ℝ) : MvPolynomial.eval Z ((∑ m ∈ s, wickTensor (A m)) ^ 2) =
      (∑ m ∈ s, ∑ w : Fin m → ι,
        A m w * MvPolynomial.eval Z (wickWord (List.ofFn w))) ^ 2 := by
    simp only [map_pow, map_sum, wickTensor_eval]
  constructor
  · convert gaussian_eval_integrable ((∑ m ∈ s, wickTensor (A m)) ^ 2) using 1
    funext Z
    exact (he Z).symm
  · simpa only [gaussianExpectation, LinearMap.coe_mk, AddHom.coe_mk, he] using
      wickTensor_sum_sq_le s A

private lemma wick_scaled_expansion_l2_bound (hn : 1 ≤ n) (k : ℕ)
    (A : (s : ℕ) → (Fin s → CoefIdxD n d) → ℝ) :
    (∫ Z, (∑ s ∈ Finset.Icc 1 k, ∑ w : Fin s → CoefIdxD n d,
      (A s w / Real.sqrt (rhoD (DD n d) s)) *
        MvPolynomial.eval Z (wickWord (List.ofFn w))) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤
      ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * frob (A s) / rhoD (DD n d) s := by
  have h := (wick_expansion_l2_bound (Finset.Icc 1 k)
    (fun s w => A s w / Real.sqrt (rhoD (DD n d) s))).2
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro s hs
  have hp := rho_pos (d := d) hn s
  simp only [frob, div_pow, Real.sq_sqrt hp.le]
  rw [← Finset.sum_div]
  ring

/-! ## P4: the error identity on the sphere -/

private lemma p4_append_val {ι : Type*} {l i : ℕ} (c : Fin l → ι) (c' : Fin i → ι)
    (u : Fin (l + i)) :
    Fin.append c c' u = if h : u.1 < l then c ⟨u.1, h⟩ else c' ⟨u.1 - l, by omega⟩ := by
  split_ifs with h
  · have : u = Fin.castAdd i ⟨u.1, h⟩ := Fin.ext rfl
    exact (congrArg (Fin.append c c') this).trans (Fin.append_left c c' _)
  · have : u = Fin.natAdd l ⟨u.1 - l, by omega⟩ := Fin.ext (by simp; omega)
    exact (congrArg (Fin.append c c') this).trans (Fin.append_right c c' _)

private lemma p4_glue_glue {ι : Type*} (j l i : ℕ) (hj : 2 * (l + i) ≤ j)
    (c : Fin l → ι) (c' : Fin i → ι) (w : Fin (j - 2 * l - 2 * i) → ι) :
    glue j l c (glue (j - 2 * l) i c' w) =
      glue j (l + i) (Fin.append c c') (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  funext t
  unfold glue
  simp only [p4_append_val]
  split_ifs <;> first
    | rfl
    | (congr 1; apply Fin.ext; simp only; omega)
    | omega

private lemma p4_trL_trL {ι R : Type*} [Fintype ι] [AddCommMonoid R] {j : ℕ} (l i : ℕ)
    (hj : 2 * (l + i) ≤ j) (A : (Fin j → ι) → R) (w : Fin (j - 2 * l - 2 * i) → ι) :
    trL i (trL l A) w = trL (l + i) A (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
  classical
  unfold trL
  rw [Finset.sum_comm]
  simp_rw [p4_glue_glue j l i hj]
  rw [← (Fin.appendEquiv l i).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Contraction is invariant under a cast of the order. -/
private lemma p4_contr_cast {ι : Type*} [Fintype ι] {a b : ℕ} (h : a = b)
    (A : (Fin a → ι) → ℝ) (v : Fin a → ι → ℝ) :
    contr A v = contr (fun w : Fin b → ι => A (fun t => w ⟨t.1, by omega⟩))
      (fun t => v ⟨t.1, by omega⟩) := by
  subst h
  rfl

private lemma p4_trL_contr {ι : Type*} [Fintype ι] {j : ℕ} (l i : ℕ)
    (hj : 2 * (l + i) ≤ j) (A : (Fin j → ι) → ℝ) (v : Fin (j - 2 * l - 2 * i) → ι → ℝ) :
    contr (trL i (trL l A)) v = contr (trL (l + i) A) (fun t => v ⟨t.1, by have := t.2; omega⟩) := by
  rw [p4_contr_cast (show j - 2 * l - 2 * i = j - 2 * (l + i) by omega)]
  congr 1
  funext w
  rw [p4_trL_trL l i hj]


private lemma p4_trL_zero {ι : Type*} [Fintype ι] {j : ℕ} (A : (Fin j → ι) → ℝ) : trL 0 A = A := by
  classical
  funext w
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

/-! ### κ–μ inversion -/

private def p2_G (k : ℕ) (w : ℚ) : ℚ := (∏ t ∈ Finset.range k, (w - 2 * t))⁻¹

private lemma p2_G_step (k : ℕ) (w : ℚ) (hw : ∀ t : ℕ, t ≤ k → w - 2 * t ≠ 0) :
    p2_G k (w - 2) - p2_G k w = 2 * k * p2_G (k + 1) w := by
  unfold p2_G
  set A := ∏ t ∈ Finset.range k, (w - 2 - 2 * (t : ℚ)) with hA
  set B := ∏ t ∈ Finset.range k, (w - 2 * (t : ℚ)) with hB
  set Q := ∏ t ∈ Finset.range (k + 1), (w - 2 * (t : ℚ)) with hQ
  have hQ1 : Q = A * w := by
    rw [hQ, Finset.prod_range_succ']
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro t ht
    push_cast; ring
  have hQ2 : Q = B * (w - 2 * k) := by rw [hQ, Finset.prod_range_succ]
  have hQ0 : Q ≠ 0 := by
    rw [hQ, Finset.prod_ne_zero_iff]
    intro t ht
    exact hw t (by simp at ht; omega)
  have hw0 : w ≠ 0 := by simpa using hw 0 (by omega)
  have hwk : w - 2 * k ≠ 0 := hw k le_rfl
  have hA0 : A ≠ 0 := by intro h; apply hQ0; rw [hQ1, h, zero_mul]
  have hB0 : B ≠ 0 := by intro h; apply hQ0; rw [hQ2, h, zero_mul]
  have h1 : A⁻¹ = w * Q⁻¹ := by rw [hQ1]; field_simp
  have h2 : B⁻¹ = (w - 2 * k) * Q⁻¹ := by rw [hQ2]; field_simp
  rw [h1, h2]; ring

private lemma p2_pascal (m : ℕ) (g : ℕ → ℚ) :
    ∑ l ∈ Finset.range (m + 2), (-1 : ℚ) ^ (m + 1 - l) * ((m + 1).choose l : ℚ) * g l =
      ∑ l ∈ Finset.range (m + 1), (-1 : ℚ) ^ (m - l) * (m.choose l : ℚ) * (g (l + 1) - g l) := by
  have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) g (m + 1) 0
  have h2 := fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) (fwdDiff 1 g) m 0
  rw [Function.iterate_succ_apply] at h1
  rw [h1] at h2
  simp only [zero_add, smul_eq_mul, mul_one, zsmul_eq_mul] at h2
  push_cast at h2
  rw [h2]
  rfl

private lemma p2_FD (y : ℚ) : ∀ m k : ℕ, (∀ u : ℕ, u < k + m → y - 2 * u ≠ 0) →
    ∑ l ∈ Finset.range (m + 1), (-1 : ℚ) ^ (m - l) * (m.choose l : ℚ) * p2_G k (y - 2 * l) =
      2 ^ m * (∏ i ∈ Finset.range m, ((k : ℚ) + i)) * p2_G (k + m) y := by
  intro m
  induction m with
  | zero => intro k hk; simp
  | succ m ih =>
    intro k hk
    rw [p2_pascal]
    have hterm : ∀ l ∈ Finset.range (m + 1),
        (-1 : ℚ) ^ (m - l) * (m.choose l : ℚ) *
          (p2_G k (y - 2 * ((l + 1 : ℕ) : ℚ)) - p2_G k (y - 2 * l)) =
        2 * k * ((-1 : ℚ) ^ (m - l) * (m.choose l : ℚ) * p2_G (k + 1) (y - 2 * l)) := by
      intro l hl
      simp only [Finset.mem_range] at hl
      have he : y - 2 * ((l + 1 : ℕ) : ℚ) = (y - 2 * l) - 2 := by push_cast; ring
      rw [he, p2_G_step]
      · ring
      · intro t ht
        have := hk (l + t) (by omega)
        push_cast at this
        intro h; apply this; linarith
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      ih (k + 1) (by intro u hu; exact hk u (by omega))]
    rw [Finset.prod_range_succ', show k + 1 + m = k + (m + 1) by ring, pow_succ]
    have hp : ∏ i ∈ Finset.range m, (((k + 1 : ℕ) : ℚ) + i) =
        ∏ i ∈ Finset.range m, ((k : ℚ) + ((i + 1 : ℕ) : ℚ)) := by
      apply Finset.prod_congr rfl; intro i hi; push_cast; ring
    rw [hp]
    simp only [Nat.cast_zero, add_zero]
    ring

private lemma p2_cQ_mul (j m l : ℕ) (hlm : l ≤ m) (hjm : 2 * m ≤ j) :
    cQ j l * cQ (j - 2 * l) (m - l) = cQ j m * (m.choose l : ℚ) := by
  have e1 : j - 2 * l - 2 * (m - l) = j - 2 * m := by omega
  have e2 : (2 : ℚ) ^ m = 2 ^ l * 2 ^ (m - l) := by rw [← pow_add]; congr 1; omega
  unfold cQ
  rw [e1, Nat.cast_choose ℚ hlm, e2]
  have := Nat.factorial_ne_zero (j - 2 * l)
  have := Nat.factorial_ne_zero (j - 2 * m)
  have := Nat.factorial_ne_zero l
  have := Nat.factorial_ne_zero m
  have := Nat.factorial_ne_zero (m - l)
  field_simp

private lemma p2_den (D : ℚ) (hD : 0 < D) (j m l : ℕ) (hlm : l ≤ m) (hjm : 2 * m ≤ j) :
    (∏ i ∈ Finset.range l, (D + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i))⁻¹ *
      (∏ t ∈ Finset.Icc 1 (m - l), (D + 2 * ((j - 2 * l : ℕ) : ℚ) - 2 - 2 * t))⁻¹ =
    p2_G m (D + 2 * j - 2 - 2 * l) + 2 * ((m : ℚ) - l) * p2_G (m + 1) (D + 2 * j - 2 - 2 * l) := by
  set v : ℚ := D + 2 * j - 2 - 2 * l with hv
  have hc : ((j - 2 * l : ℕ) : ℚ) = j - 2 * l := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hP1 : ∏ i ∈ Finset.range l, (D + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i) =
      ∏ t ∈ Finset.range l, (v - 2 * t) := by
    rw [← Finset.prod_range_reflect (fun i : ℕ => D + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * (i : ℚ)) l]
    apply Finset.prod_congr rfl
    intro t ht
    simp only [Finset.mem_range] at ht
    have h3 : ((l - 1 - t : ℕ) : ℚ) = l - 1 - t := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp only [h3, hc, hv]; ring
  have hP2 : ∏ t ∈ Finset.Icc 1 (m - l), (D + 2 * ((j - 2 * l : ℕ) : ℚ) - 2 - 2 * t) =
      ∏ x ∈ Finset.range (m - l), (v - 2 * ((l + 1 + x : ℕ) : ℚ)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    rw [Nat.add_sub_cancel]
    apply Finset.prod_congr rfl
    intro x hx
    rw [hc, hv]; push_cast; ring
  rw [hP1, hP2]
  rcases Nat.eq_or_lt_of_le hlm with h | h
  · subst h
    simp [p2_G]
  · unfold p2_G
    set A := ∏ t ∈ Finset.range l, (v - 2 * (t : ℚ))
    set B := ∏ x ∈ Finset.range (m - l), (v - 2 * ((l + 1 + x : ℕ) : ℚ))
    set C := ∏ t ∈ Finset.range m, (v - 2 * (t : ℚ))
    set Q := ∏ t ∈ Finset.range (m + 1), (v - 2 * (t : ℚ)) with hQ
    have hQ1 : Q = A * (v - 2 * l) * B := by
      rw [hQ, show m + 1 = (l + 1) + (m - l) by omega, Finset.prod_range_add,
        Finset.prod_range_succ]
    have hQ2 : Q = C * (v - 2 * m) := by rw [hQ, Finset.prod_range_succ]
    have hm : (l : ℚ) + 1 ≤ m := by exact_mod_cast h
    have hj : 2 * (m : ℚ) ≤ j := by exact_mod_cast hjm
    have hpos : ∀ t : ℕ, t ≤ m → 0 < v - 2 * t := by
      intro t ht
      have : (t : ℚ) ≤ m := by exact_mod_cast ht
      rw [hv]; linarith
    have hQ0 : Q ≠ 0 := by
      apply ne_of_gt; rw [hQ]; apply Finset.prod_pos
      intro t ht; exact hpos t (by simp at ht; omega)
    have hA0 : A ≠ 0 := by intro e; apply hQ0; rw [hQ1, e]; ring
    have hB0 : B ≠ 0 := by intro e; apply hQ0; rw [hQ1, e]; ring
    have hC0 : C ≠ 0 := by intro e; apply hQ0; rw [hQ2, e]; ring
    have hl0 : v - 2 * l ≠ 0 := (hpos l hlm).ne'
    have hm0 : v - 2 * m ≠ 0 := (hpos m le_rfl).ne'
    have h1 : A⁻¹ * B⁻¹ = (v - 2 * l) * Q⁻¹ := by rw [hQ1]; field_simp
    have h2 : C⁻¹ = (v - 2 * m) * Q⁻¹ := by rw [hQ2]; field_simp
    rw [h1, h2]; ring

private lemma p2_DQ_pos (hn : 1 ≤ n) : 0 < DQ n d := by
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
  unfold DQ
  exact_mod_cast Fintype.card_pos

private lemma p2_term (hn : 1 ≤ n) (j m l : ℕ) (hlm : l ≤ m) (hjm : 2 * m ≤ j) :
    kapQ n d j l * muQ n d (j - 2 * l) (m - l) =
      cQ j m * ((-1 : ℚ) ^ (m - l) * (m.choose l : ℚ) *
        (p2_G m (DQ n d + 2 * j - 2 - 2 * l) +
          2 * ((m : ℚ) - l) * p2_G (m + 1) (DQ n d + 2 * j - 2 - 2 * l))) := by
  have hden := p2_den (DQ n d) (p2_DQ_pos (d := d) hn) j m l hlm hjm
  have hcq := p2_cQ_mul j m l hlm hjm
  unfold kapQ muQ
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [← hden]
  linear_combination
    ((-1 : ℚ) ^ (m - l) *
      ((∏ i ∈ Finset.range l, (DQ n d + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i))⁻¹ *
      (∏ t ∈ Finset.Icc 1 (m - l), (DQ n d + 2 * ((j - 2 * l : ℕ) : ℚ) - 2 - 2 * t))⁻¹)) * hcq

private lemma p2_coef (hn : 1 ≤ n) (j m : ℕ) (hm : 1 ≤ m) (hjm : 2 * m ≤ j) :
    ∑ l ∈ Finset.range (m + 1), kapQ n d j l * muQ n d (j - 2 * l) (m - l) = 0 := by
  have hD := p2_DQ_pos (d := d) hn
  rw [Finset.sum_congr rfl (fun l hl => p2_term hn j m l
    (by simp at hl; omega) hjm), ← Finset.mul_sum]
  apply mul_eq_zero_of_right
  set y : ℚ := DQ n d + 2 * j - 2
  have hj : 2 * (m : ℚ) ≤ j := by exact_mod_cast hjm
  have hnz : ∀ u : ℕ, u < 2 * m → y - 2 * u ≠ 0 := by
    intro u hu
    have : (u : ℚ) + 1 ≤ 2 * m := by exact_mod_cast hu
    apply ne_of_gt; simp only [y]; linarith
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hA := p2_FD y (m' + 1) (m' + 1) (fun u hu => hnz u (by omega))
  have hB := p2_FD y m' (m' + 1 + 1) (fun u hu => hnz u (by omega))
  have hC : ∑ l ∈ Finset.range (m' + 1 + 1), (-1 : ℚ) ^ (m' + 1 - l) *
      ((m' + 1).choose l : ℚ) * (2 * (((m' + 1 : ℕ) : ℚ) - l) * p2_G (m' + 1 + 1) (y - 2 * l)) =
      -2 * ((m' : ℚ) + 1) * ∑ l ∈ Finset.range (m' + 1),
        (-1 : ℚ) ^ (m' - l) * (m'.choose l : ℚ) * p2_G (m' + 1 + 1) (y - 2 * l) := by
    rw [Finset.sum_range_succ, sub_self, mul_zero, zero_mul, mul_zero, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_range] at hl
    have hch : ((m' + 1).choose l : ℚ) * (((m' + 1 : ℕ) : ℚ) - l) =
        (m'.choose l : ℚ) * ((m' : ℚ) + 1) := by
      have := congrArg (fun x : ℕ => (x : ℚ)) (Nat.choose_mul_succ_eq m' l)
      simp only [Nat.cast_mul] at this
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this ⊢
      linear_combination -this
    rw [show m' + 1 - l = (m' - l) + 1 by omega, pow_succ]
    linear_combination (-2 * (-1 : ℚ) ^ (m' - l) * p2_G (m' + 1 + 1) (y - 2 * l)) * hch
  have hsplit : ∑ l ∈ Finset.range (m' + 1 + 1), (-1 : ℚ) ^ (m' + 1 - l) *
      ((m' + 1).choose l : ℚ) * (p2_G (m' + 1) (y - 2 * l) +
        2 * (((m' + 1 : ℕ) : ℚ) - l) * p2_G (m' + 1 + 1) (y - 2 * l)) =
      (∑ l ∈ Finset.range (m' + 1 + 1), (-1 : ℚ) ^ (m' + 1 - l) *
        ((m' + 1).choose l : ℚ) * p2_G (m' + 1) (y - 2 * l)) +
      ∑ l ∈ Finset.range (m' + 1 + 1), (-1 : ℚ) ^ (m' + 1 - l) *
        ((m' + 1).choose l : ℚ) * (2 * (((m' + 1 : ℕ) : ℚ) - l) * p2_G (m' + 1 + 1) (y - 2 * l)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l hl; ring
  rw [hsplit, hA, hC, hB, show m' + 1 + 1 + m' = m' + 1 + (m' + 1) by ring]
  have hprod : ∏ i ∈ Finset.range (m' + 1), (((m' + 1 : ℕ) : ℚ) + i) =
      ((m' : ℚ) + 1) * ∏ i ∈ Finset.range m', (((m' + 1 + 1 : ℕ) : ℚ) + i) := by
    rw [Finset.prod_range_succ', mul_comm]
    congr 1
    · push_cast; ring
    · apply Finset.prod_congr rfl; intro i hi; push_cast; ring
  rw [hprod]
  ring

private theorem p2_kap_mu_inversion (hn : 1 ≤ n) (j : ℕ) (X : ℕ → ℝ) :
    ∑ l ∈ Finset.range (j / 2 + 1), (kapQ n d j l : ℝ) *
      ∑ i ∈ Finset.range ((j - 2 * l) / 2 + 1), (muQ n d (j - 2 * l) i : ℝ) * X (l + i) = X 0 := by
  calc
    _ = ∑ l ∈ Finset.range (j / 2 + 1), ∑ m ∈ Finset.Ico l (j / 2 + 1),
        ((kapQ n d j l * muQ n d (j - 2 * l) (m - l) : ℚ) : ℝ) * X m := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [Finset.mem_range] at hl
      rw [Finset.mul_sum, Finset.sum_Ico_eq_sum_range,
        show j / 2 + 1 - l = (j - 2 * l) / 2 + 1 by omega]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.add_sub_cancel_left]
      push_cast; ring
    _ = ∑ m ∈ Finset.range (j / 2 + 1), ∑ l ∈ Finset.range (m + 1),
        ((kapQ n d j l * muQ n d (j - 2 * l) (m - l) : ℚ) : ℝ) * X m := by
      apply Finset.sum_comm'
      intro l m
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega
    _ = ∑ m ∈ Finset.range (j / 2 + 1),
        ((∑ l ∈ Finset.range (m + 1), kapQ n d j l * muQ n d (j - 2 * l) (m - l) : ℚ) : ℝ) *
          X m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_mul]
      push_cast; rfl
    _ = X 0 := by
      rw [Finset.sum_eq_single 0]
      · have hc : cQ j 0 = 1 := by
          unfold cQ
          have := Nat.factorial_ne_zero j
          simp [this]
        simp [kapQ, muQ, hc]
      · intro m hm hm0
        simp only [Finset.mem_range] at hm
        rw [p2_coef hn j m (by omega) (by omega)]
        simp
      · intro h; simp at h


/-- `⟨π₀ C, M^{⊗s}⟩` on the unit sphere. -/
private noncomputable def hS {s : ℕ} (C : (Fin s → CoefIdxD n d) → ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (s / 2 + 1), (muQ n d s i : ℝ) * contr (trL i C) (fun _ => M)

/-- (H2) on the sphere, in the form `⟨A, M^{⊗j}⟩ = Σ_l κ_{j,l} ⟨π₀ tr^l A, M^{⊗(j−2l)}⟩`. -/
private lemma p4_expand (hn : 1 ≤ n) {j : ℕ} (A : (Fin j → CoefIdxD n d) → ℝ)
    (M : CoefIdxD n d → ℝ) :
    contr A (fun _ => M) =
      ∑ l ∈ Finset.range (j / 2 + 1), (kapQ n d j l : ℝ) * hS (trL l A) M := by
  have h := p2_kap_mu_inversion (d := d) hn j (fun m => contr (trL m A) (fun _ => M))
  rw [p4_trL_zero] at h
  refine Eq.trans h.symm ?_
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  unfold hS
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [Finset.mem_range] at hl hi
  exact (p4_trL_contr l i (by omega) A (fun _ => M)).symm

private lemma p4_trL_add {ι : Type*} [Fintype ι] {j : ℕ} (l : ℕ) (A B : (Fin j → ι) → ℝ) :
    trL l (fun w => A w + B w) = fun w => trL l A w + trL l B w := by
  funext w
  simp only [trL, Finset.sum_add_distrib]

private lemma p4_contr_add {ι : Type*} [Fintype ι] {j : ℕ} (A B : (Fin j → ι) → ℝ)
    (v : Fin j → ι → ℝ) :
    contr (fun w => A w + B w) v = contr A v + contr B v := by
  simp only [contr, add_mul, Finset.sum_add_distrib]

private lemma p4_hS_add {s : ℕ} (A B : (Fin s → CoefIdxD n d) → ℝ) (M : CoefIdxD n d → ℝ) :
    hS (fun w => A w + B w) M = hS A M + hS B M := by
  simp only [hS, p4_trL_add, p4_contr_add, mul_add, Finset.sum_add_distrib]

private lemma p4_trL_sum {ι κ : Type*} [Fintype ι] {j : ℕ} (l : ℕ) (S : Finset κ)
    (c : κ → ℝ) (A : κ → (Fin j → ι) → ℝ) :
    trL l (fun w => ∑ x ∈ S, c x * A x w) = fun w => ∑ x ∈ S, c x * trL l (A x) w := by
  funext w
  simp only [trL, Finset.mul_sum]
  exact Finset.sum_comm

private lemma p4_contr_sum {ι κ : Type*} [Fintype ι] {j : ℕ} (S : Finset κ)
    (c : κ → ℝ) (A : κ → (Fin j → ι) → ℝ) (v : Fin j → ι → ℝ) :
    contr (fun w => ∑ x ∈ S, c x * A x w) v = ∑ x ∈ S, c x * contr (A x) v := by
  simp only [contr, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x hx
  apply Finset.sum_congr rfl; intro w hw
  ring

private lemma p4_hS_sum {κ : Type*} {s : ℕ} (S : Finset κ) (c : κ → ℝ)
    (A : κ → (Fin s → CoefIdxD n d) → ℝ) (M : CoefIdxD n d → ℝ) :
    hS (fun w => ∑ x ∈ S, c x * A x w) M = ∑ x ∈ S, c x * hS (A x) M := by
  simp only [hS, p4_trL_sum, p4_contr_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro x hx
  ring

private lemma p4_hS_cast {s s' : ℕ} (h : s' = s) (A : (Fin s' → CoefIdxD n d) → ℝ)
    (M : CoefIdxD n d → ℝ) :
    hS (fun v : Fin s → CoefIdxD n d => A (fun t => v ⟨t.1, by omega⟩)) M = hS A M := by
  subst h
  rfl


/-- The combined tensor `F ⊗ G` on `CoefIdxD = (Mono, Fin n)`. -/
private def combT {m : ℕ} (F : (Fin m → Fin n) → ℝ) (G : (Fin m → Mono n d) → ℝ) :
    (Fin m → CoefIdxD n d) → ℝ := fun v =>
  F (fun t => (v t).2.2) * G (fun t => (⟨(v t).1, (v t).2.1⟩ : Mono n d))

private lemma p4_trL_comb {j : ℕ} (l : ℕ) (F : (Fin j → Fin n) → ℝ) (G : (Fin j → Mono n d) → ℝ)
    (w : Fin (j - 2 * l) → CoefIdxD n d) :
    trL l (combT F G) w = trL l F (fun t => (w t).2.2) *
      trL l G (fun t => (⟨(w t).1, (w t).2.1⟩ : Mono n d)) := by
  classical
  have h1 (c : Fin l → CoefIdxD n d) :
      (fun t => (glue j l c w t).2.2) =
        glue j l (fun t => (c t).2.2) (fun t => (w t).2.2) := by
    funext t
    unfold glue
    by_cases ht : t.1 < 2 * l
    · rw [dite_eq_left ht, dite_eq_left ht]
    · rw [dite_eq_right ht, dite_eq_right ht]
  have h2 (c : Fin l → CoefIdxD n d) :
      (fun t => (⟨(glue j l c w t).1, (glue j l c w t).2.1⟩ : Mono n d)) =
        glue j l (fun t => (⟨(c t).1, (c t).2.1⟩ : Mono n d))
          (fun t => (⟨(w t).1, (w t).2.1⟩ : Mono n d)) := by
    funext t
    unfold glue
    by_cases ht : t.1 < 2 * l
    · rw [dite_eq_left ht, dite_eq_left ht]
    · rw [dite_eq_right ht, dite_eq_right ht]
  unfold trL combT
  simp_rw [h1, h2]
  exact combined_sum (fun c => F (glue j l c (fun t => (w t).2.2)))
    (fun p => G (glue j l p (fun t => ⟨(w t).1, (w t).2.1⟩)))

private lemma p4_contr_comb {j : ℕ} (F : (Fin j → Fin n) → ℝ) (G : (Fin j → Mono n d) → ℝ)
    (M : CoefIdxD n d → ℝ) :
    contr (combT F G) (fun _ => M) =
      ∑ w : Fin j → Mono n d, G w * contr F (fun t => colM M (w t)) := by
  classical
  let e : (Fin j → CoefIdxD n d) ≃ (Fin j → Fin n) × (Fin j → Mono n d) :=
    { toFun := fun c => (fun t => (c t).2.2, fun t => ⟨(c t).1, (c t).2.1⟩)
      invFun := fun ap t => ⟨(ap.2 t).1, ((ap.2 t).2, ap.1 t)⟩
      left_inv := fun c => rfl
      right_inv := fun ap => rfl }
  unfold contr combT
  calc
    _ = ∑ ap : (Fin j → Fin n) × (Fin j → Mono n d),
        F ap.1 * G ap.2 * ∏ t, colM M (ap.2 t) (ap.1 t) := by
      exact e.sum_comp (fun ap => F ap.1 * G ap.2 * ∏ t, colM M (ap.2 t) (ap.1 t))
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

private lemma p4_level_split (k : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 k, ∑ l ∈ Finset.range (j / 2 + 1), F j l =
      ∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j), F j (j / 2) +
        ∑ jl ∈ levels k, F jl.1 jl.2 := by
  classical
  have hlev : ∑ jl ∈ levels k, F jl.1 jl.2 =
      ∑ j ∈ Finset.Icc 1 k, ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
        F j l := by
    unfold levels
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_filter]
    simp only [Finset.mem_Icc] at hj
    rw [← Finset.sum_range_add_sum_Ico _ (show j / 2 + 1 ≤ k + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (j / 2 + 1) (k + 1))]
    · simp
    · intro l hl
      simp only [Finset.mem_Ico] at hl
      rw [if_neg (by omega)]
  rw [hlev, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (j / 2 + 1)) (fun l => 2 * l < j),
    add_comm]
  congr 1
  by_cases he : Even j
  · rw [if_pos he]
    have : (Finset.range (j / 2 + 1)).filter (fun l => ¬ 2 * l < j) = {j / 2} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      obtain ⟨r, hr⟩ := he
      omega
    rw [this, Finset.sum_singleton]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl
    exfalso
    apply he
    exact ⟨l, by omega⟩


private lemma p4_contr_order_zero {κ : Type*} [Fintype κ] {s : ℕ} (hs : s = 0)
    (A : (Fin s → κ) → ℝ) (v : Fin s → κ → ℝ) (w0 : Fin s → κ) : contr A v = A w0 := by
  subst hs
  simp only [contr, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [Fintype.sum_unique]
  congr 1
  funext t
  exact t.elim0

private lemma p4_B_side (hn : 1 ≤ n) (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    BofQ μ k f0 T M = f0 + ∑ j ∈ Finset.Icc 1 k, ∑ l ∈ Finset.range (j / 2 + 1),
      (kapQ n d j l : ℝ) * hS (combT (trL l (T j)) (fun w => (HR (n := n) (d := d) μ l w : ℝ))) M := by
  rw [B_combined hn hμ k f0 T M]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [p4_expand hn]
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  funext w
  simp only [Finset.mem_range] at hl
  exact trace_combined hn hμ j l (by omega) (T j) w

private lemma p4_level_K (hn : 1 ≤ n) (T : Tens n) (K : Finset (Multiset (Mono n d)))
    (j l : ℕ) (hl : 2 * l < j) (M : CoefIdxD n d → ℝ) :
    hS (combT (trL l (T j)) (fun w => (HKR μ (s := j - 2 * l) K l w : ℝ))) M =
      ∑ i ∈ Finset.range ((j - 2 * l) / 2 + 1), (muQ n d (j - 2 * l) i : ℝ) *
        ∑ w : Fin (j - 2 * l - 2 * i) → Mono n d,
          ((trL i (HKR μ (s := j - 2 * l) K l) w : ℝ) : ℝ) *
            contr (trL (l + i) (T j)) (fun t => colM M (w ⟨t.1, by have := t.2; omega⟩)) := by
  unfold hS
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  congr 1
  have htr : trL i (combT (trL l (T j)) (fun w => (HKR μ (s := j - 2 * l) K l w : ℝ))) =
      combT (trL i (trL l (T j))) (trL i (fun w => (HKR μ (s := j - 2 * l) K l w : ℝ))) := by
    funext w
    exact p4_trL_comb i _ _ w
  rw [htr, p4_contr_comb]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  exact p4_trL_contr l i (by omega) (T j) (fun t => colM M (w t))

private lemma p4_level_zero (T : Tens n) (j : ℕ) (hj : Even j) (M : CoefIdxD n d → ℝ) :
    hS (combT (trL (j / 2) (T j)) (fun w => (HR (n := n) (d := d) μ (j / 2) w : ℝ))) M =
      (HR (n := n) (d := d) μ (s := j - 2 * (j / 2)) (j / 2) (fun _ => default) : ℝ) *
        contr (trL (j / 2) (T j)) (fun _ _ => 0) := by
  have hs : j - 2 * (j / 2) = 0 := by obtain ⟨r, hr⟩ := hj; omega
  unfold hS
  rw [show (j - 2 * (j / 2)) / 2 = 0 by omega, Finset.sum_range_one]
  have hmu : (muQ n d (j - 2 * (j / 2)) 0 : ℝ) = 1 := by
    simp [muQ, cQ, Nat.factorial_ne_zero]
  rw [hmu, one_mul, p4_trL_zero]
  let w0 : Fin (j - 2 * (j / 2)) → CoefIdxD n d := fun t => absurd t.2 (by omega)
  rw [p4_contr_order_zero hs _ _ w0,
    p4_contr_order_zero hs (trL (j / 2) (T j)) _ (fun t => (w0 t).2.2)]
  unfold combT
  rw [mul_comm]
  congr 3
  funext t
  exact absurd t.2 (by omega)


private lemma p4_error_levels (hn : 1 ≤ n) (hμ : SphLaw n μ) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    BofQ μ k f0 T M - gTCR μ k K f0 T M = ∑ jl ∈ levels k, (kapQ n d jl.1 jl.2 : ℝ) *
      hS (combT (trL jl.2 (T jl.1))
        (fun w => (RR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2 w : ℝ))) M := by
  rw [p4_B_side hn hμ, p4_level_split k (fun j l => (kapQ n d j l : ℝ) *
    hS (combT (trL l (T j)) (fun w => (HR (n := n) (d := d) μ l w : ℝ))) M)]
  unfold gTCR
  have heven : ∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j), (kapQ n d j (j / 2) : ℝ) *
      hS (combT (trL (j / 2) (T j)) (fun w => (HR (n := n) (d := d) μ (j / 2) w : ℝ))) M =
      ∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j),
        (kapQ n d j (j / 2) : ℝ) *
          (HR (n := n) (d := d) μ (s := j - 2 * (j / 2)) (j / 2) (fun _ => default) : ℝ) *
            contr (trL (j / 2) (T j)) (fun _ _ => 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [p4_level_zero T j (Finset.mem_filter.mp hj).2 M, mul_assoc]
  rw [heven]
  have hlev : ∑ jl ∈ levels k, (kapQ n d jl.1 jl.2 : ℝ) *
      hS (combT (trL jl.2 (T jl.1)) (fun w => (HR (n := n) (d := d) μ jl.2 w : ℝ))) M =
      ∑ jl ∈ levels k, (kapQ n d jl.1 jl.2 : ℝ) *
        ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1), (muQ n d (jl.1 - 2 * jl.2) i : ℝ) *
          ∑ w : Fin (jl.1 - 2 * jl.2 - 2 * i) → Mono n d,
            ((trL i (HKR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2) w : ℝ) : ℝ) *
              contr (trL (jl.2 + i) (T jl.1)) (fun t => colM M (w ⟨t.1, by have := t.2; omega⟩)) +
      ∑ jl ∈ levels k, (kapQ n d jl.1 jl.2 : ℝ) *
        hS (combT (trL jl.2 (T jl.1))
          (fun w => (RR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2 w : ℝ))) M := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro jl hjl
    have h2 : 2 * jl.2 < jl.1 := by
      simp only [levels, Finset.mem_filter] at hjl
      exact hjl.2
    rw [← p4_level_K hn T (K jl.1 jl.2) jl.1 jl.2 h2 M, ← mul_add, ← p4_hS_add]
    congr 2
    funext v
    unfold combT
    rw [← mul_add]
    congr 1
    simp only [RR]
    ring
  rw [hlev]
  ring


/-- The error tensor `W_s` on the combined index. -/
private noncomputable def Wt (μ : Measure (Fin n → ℝ)) (k s : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (T : Tens n) :
    (Fin s → CoefIdxD n d) → ℝ := fun v =>
  ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
    (kapQ n d (s + 2 * l) l : ℝ) *
      combT (trL l (T (s + 2 * l)))
        (fun w => (RR μ (s := s + 2 * l - 2 * l) (K (s + 2 * l) l) l w : ℝ))
        (fun t => v ⟨t.1, by have := t.2; omega⟩)

private lemma p4_regroup (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (T : Tens n)
    (M : CoefIdxD n d → ℝ) :
    ∑ jl ∈ levels k, (kapQ n d jl.1 jl.2 : ℝ) *
      hS (combT (trL jl.2 (T jl.1))
        (fun w => (RR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2 w : ℝ))) M =
      ∑ s ∈ Finset.Icc 1 k, hS (Wt μ k s K T) M := by
  rw [← regroup_levels k (fun j l => (kapQ n d j l : ℝ) *
    hS (combT (trL l (T j)) (fun w => (RR μ (s := j - 2 * l) (K j l) l w : ℝ))) M)]
  apply Finset.sum_congr rfl
  intro s hs
  unfold Wt
  rw [p4_hS_sum]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  exact (p4_hS_cast (show s + 2 * l - 2 * l = s by omega) _ M).symm

private lemma p4_frob_Wt (k s : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (T : Tens n) :
    frob (Wt μ k s K T) = WfrobSqR μ k s K T := by
  classical
  let e : (Fin s → CoefIdxD n d) ≃ (Fin s → Fin n) × (Fin s → Mono n d) :=
    { toFun := fun c => (fun t => (c t).2.2, fun t => ⟨(c t).1, (c t).2.1⟩)
      invFun := fun ap t => ⟨(ap.2 t).1, ((ap.2 t).2, ap.1 t)⟩
      left_inv := fun c => rfl
      right_inv := fun ap => rfl }
  unfold frob WfrobSqR
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro q hq
  congr 1
  unfold Wt combT
  apply Finset.sum_congr rfl; intro l hl
  rw [← mul_assoc]
  rfl


/-- The partial trace of a symmetric tensor is symmetric. -/
private theorem p4_trL_symm {ι R : Type*} [Fintype ι] [AddCommMonoid R] {j : ℕ} (l : ℕ) (hl : 2 * l ≤ j)
    (A : (Fin j → ι) → R) (hA : IsSymmT A) : IsSymmT (trL l A) := by
  classical
  intro σ w
  let e : Fin (j - 2 * l) ≃ {t : Fin j // 2 * l ≤ t.val} :=
    { toFun := fun t => ⟨⟨2 * l + t.val, by omega⟩, by simp⟩
      invFun := fun t => ⟨t.val.val - 2 * l, by have := t.val.isLt; have := t.property; omega⟩
      left_inv := by intro t; apply Fin.ext; simp
      right_inv := by intro t; apply Subtype.ext; apply Fin.ext; simp; have := t.property; omega }
  let τ := σ.extendDomain e
  unfold trL
  apply Finset.sum_congr rfl
  intro c hc
  have heq : glue j l c (w ∘ σ) = glue j l c w ∘ τ := by
    funext t
    by_cases ht : t.val < 2 * l
    · have hτ : τ t = t := σ.extendDomain_apply_not_subtype e (by omega)
      simp [hτ, glue, ht]
    · let u : Fin (j - 2 * l) := ⟨t.val - 2 * l, by have := t.isLt; omega⟩
      have hu : (e u).val = t := by apply Fin.ext; dsimp [e, u]; omega
      have hτ : τ t = (e (σ u)).val := by
        rw [← hu]
        exact σ.extendDomain_apply_image e u
      simp [glue, ht, hτ, e, u]
  rw [heq]
  exact hA τ (glue j l c w)

private theorem p4_HQ_symm {s : ℕ} (l : ℕ) :
    IsSymmT (fun w : Fin s → Mono n d => HR μ l w) := by
  intro σ w
  unfold HR
  apply integral_congr_ae
  exact ae_of_all _ (fun x => congrArg (fun z => phiSq d x ^ l * z)
    (Equiv.prod_comp σ (fun t => phiM x (w t))))

private lemma p4_HK_symm {s : ℕ} (K : Finset (Multiset (Mono n d))) (l : ℕ) :
    IsSymmT (HKR μ (s := s) K l) := by
  classical
  intro σ w
  have hm : mset (w ∘ σ) = mset w := by
    simp only [mset, Fin.univ_val_map]
    exact Quot.sound (σ.ofFn_comp_perm w)
  unfold HKR
  rw [hm]
  split_ifs
  · exact p4_HQ_symm l σ w
  · rfl

private lemma p4_comb_symm {m : ℕ} (F : (Fin m → Fin n) → ℝ) (G : (Fin m → Mono n d) → ℝ)
    (hF : IsSymmT F) (hG : IsSymmT G) : IsSymmT (combT F G) := by
  intro σ v
  unfold combT
  exact congrArg₂ (· * ·) (hF σ (fun t => (v t).2.2))
    (hG σ (fun t => (⟨(v t).1, (v t).2.1⟩ : Mono n d)))

private lemma p4_cast_symm {ι : Type*} {a b : ℕ} (h : a = b) (A : (Fin a → ι) → ℝ)
    (hA : IsSymmT A) : IsSymmT (fun v : Fin b → ι => A (fun t => v ⟨t.1, by omega⟩)) := by
  subst h
  exact hA

private lemma p4_Wt_symm (k s : ℕ) (hs : 1 ≤ s) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (T : Tens n) (hT : TSymm k T) : IsSymmT (Wt μ k s K T) := by
  intro σ v
  unfold Wt
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_range] at hl
  congr 1
  have hR : IsSymmT (fun w : Fin (s + 2 * l - 2 * l) → Mono n d =>
      (RR μ (s := s + 2 * l - 2 * l) (K (s + 2 * l) l) l w : ℝ)) := by
    intro τ w
    have h1 := p4_HQ_symm (μ := μ) (n := n) (d := d) (s := s + 2 * l - 2 * l) l τ w
    have h2 := p4_HK_symm (μ := μ) (s := s + 2 * l - 2 * l) (K (s + 2 * l) l) l τ w
    simp only [RR] at h1 h2 ⊢
    rw [h1, h2]
  have hC := p4_comb_symm _ _ (p4_trL_symm l (by omega) (T (s + 2 * l))
    (hT _ (by omega) hl.2)) hR
  exact p4_cast_symm (show s + 2 * l - 2 * l = s by omega) _ hC σ v


/-! ## P1: Gaussian polar coordinates -/

private lemma p1_density {ι : Type*} [Fintype ι] :
    stdGauss ι = (volume : Measure (ι → ℝ)).withDensity
      (fun x => ∏ i, ProbabilityTheory.gaussianPDF 0 1 (x i)) := by
  unfold stdGauss
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  have hint : Integrable (fun x : ι → ℝ => ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i))
      (Measure.pi fun i => (volume : Measure ℝ).restrict (s i)) :=
    Integrable.fintype_prod (fun i => (ProbabilityTheory.integrable_gaussianPDFReal 0 1).restrict)
  have h1 : (fun x : ι → ℝ => ∏ i, ProbabilityTheory.gaussianPDF 0 1 (x i)) =
      fun x => ENNReal.ofReal (∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (x i)) := by
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)]
    rfl
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ =>
      ProbabilityTheory.gaussianPDFReal_nonneg _ _ _))),
    integral_fintype_prod_eq_prod (f := fun _ x => ProbabilityTheory.gaussianPDFReal 0 1 x),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => setIntegral_nonneg_of_ae (ae_of_all _
      (fun x => ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral _ one_ne_zero]

private lemma p1_integral {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) :
    ∫ Z, f Z ∂stdGauss ι = (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
      ∫ x : EuclideanSpace ℝ ι, f (WithLp.ofLp x) * Real.exp (-‖x‖ ^ 2 / 2) := by
  have hm : Measurable (fun x : ι → ℝ => ∏ i, ProbabilityTheory.gaussianPDF 0 1 (x i)) :=
    Finset.measurable_prod _ (fun i _ =>
      (ProbabilityTheory.measurable_gaussianPDF 0 1).comp (measurable_pi_apply i))
  rw [p1_density, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun x => ENNReal.prod_lt_top (fun i _ =>
      ProbabilityTheory.gaussianPDF_lt_top)))]
  have hd (x : ι → ℝ) : (∏ i, ProbabilityTheory.gaussianPDF 0 1 (x i)).toReal =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-(∑ i, x i ^ 2) / 2) := by
    rw [ENNReal.toReal_prod]
    simp only [ProbabilityTheory.toReal_gaussianPDF, ProbabilityTheory.gaussianPDFReal,
      NNReal.coe_one, mul_one, sub_zero]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
    congr 2
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    simp [neg_div]
  simp_rw [hd, smul_eq_mul]
  rw [← integral_const_mul]
  have h := (PiLp.volume_preserving_ofLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding
    (fun x : ι → ℝ => (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
      Real.exp (-(∑ i, x i ^ 2) / 2) * f x)
  rw [← h]
  congr 1
  funext x
  rw [EuclideanSpace.real_norm_sq_eq]
  ring

private lemma p1_polar {ι : Type*} [Fintype ι] [Nonempty ι] (k : ℕ) (P : EuclideanSpace ℝ ι → ℝ)
    (hP : ∀ (u : Metric.sphere (0 : EuclideanSpace ℝ ι) 1)
      (r : ℝ), 0 < r → P (r • u.1) = r ^ k * P u.1) :
    (∫ x, P x * Real.exp (-‖x‖ ^ 2 / 2)) =
      (∫ u : Metric.sphere (0 : EuclideanSpace ℝ ι) 1, P u.1
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) *
      ∫ r in Set.Ioi (0 : ℝ), r ^ (Fintype.card ι - 1 + k) * Real.exp (-r ^ 2 / 2) := by
  let E := EuclideanSpace ℝ ι
  let μ : Measure E := volume
  let f := fun z : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
    P z.1.1 * (z.2.1 ^ k * Real.exp (-z.2.1 ^ 2 / 2))
  have hcomp : ∀ x : ({(0 : E)}ᶜ : Set E),
      f (homeomorphUnitSphereProd E x) = P x.1 * Real.exp (-‖x.1‖ ^ 2 / 2) := by
    intro x
    let z := homeomorphUnitSphereProd E x
    have hx : x.1 = z.2.1 • z.1.1 := by
      have h := congrArg Subtype.val ((homeomorphUnitSphereProd E).symm_apply_apply x)
      rw [homeomorphUnitSphereProd_symm_apply_coe] at h
      exact h.symm
    rw [hx]
    have hu : ‖z.1.1‖ = 1 := by simp
    change P z.1.1 * (z.2.1 ^ k * Real.exp (-z.2.1 ^ 2 / 2)) = _
    rw [hP z.1 z.2.1 z.2.2, norm_smul, Real.norm_eq_abs, abs_of_pos z.2.2, hu,
      mul_one]
    ring
  calc
    _ = ∫ x : ({(0 : E)}ᶜ : Set E), P x.1 * Real.exp (-‖x.1‖ ^ 2 / 2)
        ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x => P x * Real.exp (-‖x‖ ^ 2 / 2)),
        restrict_compl_singleton]
    _ = ∫ z, f z ∂μ.toSphere.prod (.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      simpa only [Function.comp_def, hcomp] using
        μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _) f
    _ = (∫ u, P u.1 ∂μ.toSphere) *
        ∫ r : Set.Ioi (0 : ℝ), r.1 ^ k * Real.exp (-r.1 ^ 2 / 2)
          ∂Measure.volumeIoiPow (Fintype.card ι - 1) := by
      simpa [f, E] using integral_prod_mul
        (fun u : Metric.sphere (0 : E) 1 => P u.1)
        (fun r : Set.Ioi (0 : ℝ) => r.1 ^ k * Real.exp (-r.1 ^ 2 / 2))
    _ = _ := by
      congr 1
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul
        ((measurable_subtype_coe.pow_const _).real_toNNReal)]
      rw [integral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => Real.toNNReal (r ^ (Fintype.card ι - 1)) •
          (r ^ k * Real.exp (-r ^ 2 / 2)))]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _),
        pow_add]
      ring


private lemma p1_radial_value (n k : ℕ) (hn : 1 ≤ n) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1 + k) * Real.exp (-r ^ 2 / 2)) =
      (1 / 2 : ℝ) ^ (-((n + k : ℕ) : ℝ) / 2) * (1 / 2) *
        Real.Gamma (((n + k : ℕ) : ℝ) / 2) := by
  have hc : ((n - 1 + k : ℕ) : ℝ) + 1 = ((n + k : ℕ) : ℝ) := by
    exact_mod_cast (show n - 1 + k + 1 = n + k by omega)
  convert integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := ((n - 1 + k : ℕ) : ℝ)) (b := 1 / 2)
    (by norm_num) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
    (by norm_num) using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [Real.rpow_natCast, Real.rpow_two]
    congr 2
    ring
  · rw [hc]

private lemma p1_radial_pos (n k : ℕ) (hn : 1 ≤ n) :
    0 < ∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1 + k) * Real.exp (-r ^ 2 / 2) := by
  rw [p1_radial_value n k hn]
  have hg : 0 < Real.Gamma (((n + k : ℕ) : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (div_pos (by exact_mod_cast (show 0 < n + k by omega))
      (by norm_num))
  positivity

private lemma p1_radial_step (n k : ℕ) (hn : 1 ≤ n) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1 + (k + 2)) * Real.exp (-r ^ 2 / 2)) =
      (n + k : ℝ) * ∫ r in Set.Ioi (0 : ℝ),
        r ^ (n - 1 + k) * Real.exp (-r ^ 2 / 2) := by
  rw [p1_radial_value n (k + 2) hn, p1_radial_value n k hn]
  have ha : (((n + (k + 2) : ℕ) : ℝ) / 2) = ((n + k : ℕ) : ℝ) / 2 + 1 := by
    push_cast
    ring
  rw [ha, Real.Gamma_add_one
    (ne_of_gt (div_pos (by exact_mod_cast (show 0 < n + k by omega)) (by norm_num)))]
  have hb : -((n + (k + 2) : ℕ) : ℝ) / 2 = -((n + k : ℕ) : ℝ) / 2 + (-1) := by
    push_cast
    ring
  rw [hb, Real.rpow_add (by norm_num), Real.rpow_neg_one]
  norm_num
  ring


private lemma p1_radial_even (n j : ℕ) (hn : 1 ≤ n) :
    (∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (n - 1 + 2 * j) * Real.exp (-ρ ^ 2 / 2)) =
      (∏ a ∈ Finset.range j, (n + 2 * a : ℝ)) *
        ∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (n - 1) * Real.exp (-ρ ^ 2 / 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, p1_radial_step n (2 * j) hn, ih,
      Finset.prod_range_succ]
    push_cast
    ring


private lemma p1_sqrt_norm {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    Real.sqrt (∑ i, (WithLp.ofLp x) i ^ 2) = ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, sq_abs]

private lemma p1_sphere_norm {ι : Type*} [Fintype ι]
    (u : Metric.sphere (0 : EuclideanSpace ℝ ι) 1) : ‖u.1‖ = 1 := by simp

private lemma p1_main {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℕ) (P : (ι → ℝ) → ℝ)
    (hP : ∀ c : ℝ, 0 < c → ∀ Z, P (c • Z) = c ^ r * P Z) :
    let σ := (volume : Measure (EuclideanSpace ℝ ι)).toSphere
    let R := fun k : ℕ => ∫ ρ in Set.Ioi (0 : ℝ),
      ρ ^ (Fintype.card ι - 1 + k) * Real.exp (-ρ ^ 2 / 2)
    let c := (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι
    (∫ Z, P Z ∂stdGauss ι) = c * ((∫ u : Metric.sphere (0 : EuclideanSpace ℝ ι) 1,
        P (WithLp.ofLp u.1) ∂σ) * R r) ∧
    (∫ Z, P ((1 / Real.sqrt (∑ i, Z i ^ 2)) • Z) ∂stdGauss ι) =
      c * ((∫ u : Metric.sphere (0 : EuclideanSpace ℝ ι) 1,
        P (WithLp.ofLp u.1) ∂σ) * R 0) ∧
    (∫ Z, Real.sqrt (∑ i, Z i ^ 2) ^ r ∂stdGauss ι) = c * (σ.real Set.univ * R r) ∧
    c * (σ.real Set.univ * R 0) = 1 := by
  intro σ R c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p1_integral]
    congr 1
    exact p1_polar r (fun x => P (WithLp.ofLp x)) (by
      intro u ρ hρ
      simp only [WithLp.ofLp_smul]
      exact hP ρ hρ _)
  · rw [p1_integral]
    congr 1
    simp_rw [p1_sqrt_norm]
    have h := p1_polar 0 (fun x : EuclideanSpace ℝ ι => P ((1 / ‖x‖) • WithLp.ofLp x)) (by
      intro u ρ hρ
      simp only [WithLp.ofLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
        p1_sphere_norm, mul_one, pow_zero, one_mul, smul_smul]
      congr 2
      field_simp)
    rw [h]
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro u
    simp
  · rw [p1_integral]
    congr 1
    simp_rw [p1_sqrt_norm]
    have h := p1_polar r (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ r) (by
      intro u ρ hρ
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow])
    rw [h]
    congr 1
    simp only [p1_sphere_norm, one_pow, integral_const, smul_eq_mul, mul_one]
    rfl
  · have h1 := p1_integral (ι := ι) (fun _ => 1)
    have h := p1_polar 0 (fun _ : EuclideanSpace ℝ ι => (1 : ℝ)) (by simp)
    simp only [one_mul, integral_const, smul_eq_mul, mul_one, probReal_univ] at h1 h
    rw [h] at h1
    exact h1.symm

private theorem p1_gauss_polar {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℕ) (P : (ι → ℝ) → ℝ)
    (hP : ∀ c : ℝ, 0 < c → ∀ Z, P (c • Z) = c ^ r * P Z) :
    ∫ Z, P Z ∂stdGauss ι =
      (∫ Z, P ((1 / Real.sqrt (∑ i, Z i ^ 2)) • Z) ∂stdGauss ι) *
        ∫ Z, Real.sqrt (∑ i, Z i ^ 2) ^ r ∂stdGauss ι := by
  obtain ⟨h1, h2, h3, h4⟩ := p1_main r P hP
  rw [h1, h2, h3]
  linear_combination (-((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
    (∫ u : Metric.sphere (0 : EuclideanSpace ℝ ι) 1, P (WithLp.ofLp u.1)
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) *
    ∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (Fintype.card ι - 1 + r) * Real.exp (-ρ ^ 2 / 2))) * h4

private lemma p1_norm_ratio {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℕ) :
    ∫ Z, Real.sqrt (∑ i, Z i ^ 2) ^ r ∂stdGauss ι =
      (∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (Fintype.card ι - 1 + r) * Real.exp (-ρ ^ 2 / 2)) /
      (∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (Fintype.card ι - 1 + 0) * Real.exp (-ρ ^ 2 / 2)) := by
  obtain ⟨-, -, h3, h4⟩ := p1_main (ι := ι) r (fun _ => (0 : ℝ)) (by simp)
  have hR0 := p1_radial_pos (Fintype.card ι) 0 Fintype.card_pos
  rw [h3, eq_div_iff hR0.ne']
  linear_combination (∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (Fintype.card ι - 1 + r) *
    Real.exp (-ρ ^ 2 / 2)) * h4

private theorem p1_gauss_norm_pos {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℕ) :
    0 < ∫ Z, Real.sqrt (∑ i, Z i ^ 2) ^ r ∂stdGauss ι := by
  rw [p1_norm_ratio]
  exact div_pos (p1_radial_pos _ r Fintype.card_pos) (p1_radial_pos _ 0 Fintype.card_pos)

private theorem p1_gauss_norm_moment {ι : Type*} [Fintype ι] (s : ℕ) :
    ∫ Z, Real.sqrt (∑ i, Z i ^ 2) ^ (2 * s) ∂stdGauss ι = rhoD (Fintype.card ι) s := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.sqrt_zero, integral_const,
      probReal_univ, smul_eq_mul, one_mul, Fintype.card_eq_zero, Nat.cast_zero]
    unfold rhoD
    cases s with
    | zero => simp
    | succ s =>
      rw [zero_pow (by omega)]
      symm
      exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos s)) (by simp)
  · rw [p1_norm_ratio, p1_radial_even _ s Fintype.card_pos]
    have hR0 := p1_radial_pos (Fintype.card ι) 0 Fintype.card_pos
    simp only [add_zero] at hR0 ⊢
    rw [mul_div_assoc, div_self hR0.ne', mul_one]
    rfl


/-! ## P3c: Gaussian facts for harmonic homogeneous polynomials -/

private noncomputable def lapP {ι : Type*} [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι ℝ) :
    MvPolynomial ι ℝ := ∑ a, MvPolynomial.pderiv a (MvPolynomial.pderiv a p)
private noncomputable def plainT {ι : Type*} [Fintype ι] {m : ℕ} (A : (Fin m → ι) → ℝ) :
    MvPolynomial ι ℝ := ∑ w, MvPolynomial.C (A w) * ∏ t, MvPolynomial.X (w t)
private noncomputable def sqN {ι : Type*} [Fintype ι] : MvPolynomial ι ℝ :=
  ∑ a, MvPolynomial.X a ^ 2

private lemma p3c_pderiv_comm {ι : Type*} [DecidableEq ι] (i j : ι) (p : MvPolynomial ι ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  ext m
  simp only [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst hij; rfl
  · have h1 : (m + Finsupp.single i 1 : ι →₀ ℕ) j = m j := by
      simp [hij]
    have h2 : (m + Finsupp.single j 1 : ι →₀ ℕ) i = m i := by
      simp [Ne.symm hij]
    rw [h1, h2, add_right_comm m (Finsupp.single i 1) (Finsupp.single j 1)]
    ring

private lemma p3c_lap_pderiv {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι)
    (p : MvPolynomial ι ℝ) :
    lapP (MvPolynomial.pderiv b p) = MvPolynomial.pderiv b (lapP p) := by
  unfold lapP
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [p3c_pderiv_comm a b, p3c_pderiv_comm a b]

private lemma p3c_euler_E {ι : Type*} [Fintype ι] [DecidableEq ι] (p F : MvPolynomial ι ℝ)
    (s : ℕ) (hp : p.IsHomogeneous s) :
    (s : ℝ) * gaussianExpectation (p * F) =
      gaussianExpectation (lapP p * F) +
        ∑ a, gaussianExpectation (MvPolynomial.pderiv a p * MvPolynomial.pderiv a F) := by
  have he := hp.sum_X_mul_pderiv
  have h1 : (s : ℝ) * gaussianExpectation (p * F) =
      gaussianExpectation ((∑ a, MvPolynomial.X a * MvPolynomial.pderiv a p) * F) := by
    rw [he, nsmul_eq_mul, mul_assoc, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ),
      gaussianExpectation_C_mul]
  rw [h1, Finset.sum_mul, map_sum, lapP, Finset.sum_mul, map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc, gaussianExpectation_X_mul, MvPolynomial.pderiv_mul, map_add]

private lemma p3c_low {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (s : ℕ) (p : MvPolynomial ι ℝ), p.IsHomogeneous s → lapP p = 0 →
      ∀ G : MvPolynomial ι ℝ, G.totalDegree < s → gaussianExpectation (p * G) = 0 := by
  intro s
  induction s with
  | zero => intro p _ _ G hG; omega
  | succ s ih =>
    intro p hp hL G hG
    have h := p3c_euler_E p G (s + 1) hp
    rw [hL, zero_mul, map_zero, zero_add] at h
    have hz : ∑ a, gaussianExpectation (MvPolynomial.pderiv a p * MvPolynomial.pderiv a G) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have hpa : (MvPolynomial.pderiv a p).IsHomogeneous s := by
        simpa using hp.pderiv (i := a)
      have hLa : lapP (MvPolynomial.pderiv a p) = 0 := by
        rw [p3c_lap_pderiv, hL, map_zero]
      have hd := pderiv_degree a G
      by_cases hs : s = 0
      · subst hs
        have hG0 : G.totalDegree = 0 := by omega
        rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hG0, MvPolynomial.pderiv_C,
          mul_zero, map_zero]
      · exact ih _ hpa hLa _ (by omega)
    rw [hz] at h
    have hs : ((s + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h).resolve_left hs

private lemma harmonic_orth {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : MvPolynomial ι ℝ) (s t : ℕ)
    (hp : p.IsHomogeneous s) (hq : q.IsHomogeneous t) (hLp : lapP p = 0) (hLq : lapP q = 0)
    (hst : s ≠ t) : gaussianExpectation (p * q) = 0 := by
  rcases lt_or_gt_of_ne hst with h | h
  · rw [mul_comm]
    exact p3c_low t q hq hLq p (lt_of_le_of_lt hp.totalDegree_le h)
  · exact p3c_low s p hp hLp q (lt_of_le_of_lt hq.totalDegree_le h)

private lemma p3c_sq_nonneg {ι : Type*} [Fintype ι] (q : MvPolynomial ι ℝ) :
    0 ≤ gaussianExpectation (q ^ 2) := by
  simp only [gaussianExpectation, LinearMap.coe_mk, AddHom.coe_mk]
  exact integral_nonneg (fun Z => by simp only [map_pow]; positivity)

private lemma p3c_sqN_orth {ι : Type*} [Fintype ι] [DecidableEq ι] (p r : MvPolynomial ι ℝ)
    (s : ℕ) (hp : p.IsHomogeneous s) (hL : lapP p = 0)
    (hr : r = 0 ∨ (2 ≤ s ∧ r.IsHomogeneous (s - 2))) :
    gaussianExpectation (p * (sqN * r)) = 0 := by
  rcases hr with hr | ⟨hs, hr⟩
  · rw [hr, mul_zero, mul_zero, map_zero]
  have hpr : (p * r).IsHomogeneous (s + (s - 2)) := hp.mul hr
  have hE := hpr.sum_X_mul_pderiv
  have hkey : gaussianExpectation (p * (sqN * r)) =
      ((Fintype.card ι : ℝ) + ((s + (s - 2) : ℕ) : ℝ)) * gaussianExpectation (p * r) := by
    have h1 : p * (sqN * r) = ∑ a, MvPolynomial.X a * (MvPolynomial.X a * (p * r)) := by
      unfold sqN
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have h2 : ∀ a, gaussianExpectation (MvPolynomial.X a * (MvPolynomial.X a * (p * r))) =
        gaussianExpectation (p * r) +
          gaussianExpectation (MvPolynomial.X a * MvPolynomial.pderiv a (p * r)) := by
      intro a
      rw [gaussianExpectation_X_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
        one_mul, map_add]
    rw [h1, map_sum]
    simp_rw [h2]
    rw [Finset.sum_add_distrib,
      ← map_sum gaussianExpectation (fun a => MvPolynomial.X a * MvPolynomial.pderiv a (p * r)), hE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      nsmul_eq_mul, ← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial ι ℝ),
      gaussianExpectation_C_mul]
    ring
  rw [hkey, p3c_low s p hp hL r (lt_of_le_of_lt hr.totalDegree_le (by omega)), mul_zero]

private lemma p3c_plain_wick {ι : Type*} [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι ℝ)
    (s : ℕ) (hp : p.IsHomogeneous s) (hL : lapP p = 0) (W : (Fin s → ι) → ℝ) :
    gaussianExpectation (p * plainT W) = gaussianExpectation (p * wickTensor W) := by
  have hd : plainT W - wickTensor W =
      ∑ w : Fin s → ι, MvPolynomial.C (W w) *
        (plainWord (List.ofFn w) - wickWord (List.ofFn w)) := by
    unfold plainT wickTensor
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [plainWord_ofFn]
    ring
  have h0 : gaussianExpectation (p * (plainT W - wickTensor W)) = 0 := by
    by_cases hs : s = 0
    · subst hs
      rw [hd]
      have : ∀ w : Fin 0 → ι, plainWord (List.ofFn w) - wickWord (List.ofFn w) = 0 := by
        intro w; simp [plainWord, wickWord]
      simp only [this, mul_zero, Finset.sum_const_zero, map_zero]
    · apply p3c_low s p hp hL
      rw [hd]
      refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
      rw [Finset.sup_lt_iff (by simpa using Nat.pos_of_ne_zero hs)]
      intro w _
      refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      have := wickWord_remainder_degree (List.ofFn w)
      simp only [List.length_ofFn] at this
      omega
  rw [mul_sub, map_sub, sub_eq_zero] at h0
  exact h0

private lemma harmonic_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι ℝ) (s : ℕ)
    (hp : p.IsHomogeneous s) (hL : lapP p = 0) (W : (Fin s → ι) → ℝ) (r : MvPolynomial ι ℝ)
    (hr : r = 0 ∨ (2 ≤ s ∧ r.IsHomogeneous (s - 2))) (hpr : p = plainT W + sqN * r) :
    gaussianExpectation (p ^ 2) ≤ (s.factorial : ℝ) * frob W := by
  have ha : gaussianExpectation (p ^ 2) = gaussianExpectation (p * wickTensor W) := by
    have h1 : gaussianExpectation (p ^ 2) =
        gaussianExpectation (p * plainT W) + gaussianExpectation (p * (sqN * r)) := by
      rw [← map_add, ← mul_add, ← hpr, pow_two]
    rw [h1, p3c_sqN_orth p r s hp hL hr, add_zero, p3c_plain_wick p s hp hL W]
  have hb := wickTensor_sq_le W
  have hn := p3c_sq_nonneg (p - wickTensor W)
  have hexp : (p - wickTensor W) ^ 2 =
      p ^ 2 - MvPolynomial.C (2 : ℝ) * (p * wickTensor W) + wickTensor W ^ 2 := by
    rw [map_ofNat]; ring
  rw [hexp, map_add, map_sub, gaussianExpectation_C_mul] at hn
  unfold wickTensor at hb ha hn
  unfold frob
  linarith

/-! ## P3b: the harmonic polynomial `⟨π₀ W, Z^{⊗s}⟩` -/
private noncomputable def hPoly {s : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ) :
    MvPolynomial (CoefIdxD n d) ℝ :=
  ∑ i ∈ Finset.range (s / 2 + 1), MvPolynomial.C (muQ n d s i : ℝ) * sqN ^ i * plainT (trL i W)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
section p3b
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def p3b_sl {p : ℕ} (A : (Fin (p + 1) → ι) → ℝ) (a : ι) : (Fin p → ι) → ℝ :=
  fun w => A (Fin.cons a w)

private lemma p3b_sum_cons {p : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (p + 1) → ι) → M) :
    ∑ w, f w = ∑ a, ∑ w : Fin p → ι, f (Fin.cons a w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (p + 1) => ι)).sum_comp, Fintype.sum_prod_type]
  rfl

private lemma p3b_peel {p : ℕ} (A : (Fin (p + 1) → ι) → ℝ) :
    plainT A = ∑ a, MvPolynomial.X a * plainT (p3b_sl A a) := by
  unfold plainT p3b_sl
  rw [p3b_sum_cons]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

private lemma p3b_zero (A : (Fin 0 → ι) → ℝ) :
    plainT A = MvPolynomial.C (A Fin.elim0) := by
  unfold plainT
  rw [Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  congr 2

private lemma p3b_sl_symm {p : ℕ} {A : (Fin (p + 1) → ι) → ℝ} (hA : IsSymmT A) (a : ι) :
    IsSymmT (p3b_sl A a) := by
  intro σ w
  have h := hA (Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.cons a w)
  unfold p3b_sl
  rw [← h]
  congr 1
  funext t
  refine Fin.cases ?_ (fun t => ?_) t
  · simp
  · simp [Equiv.Perm.decomposeFin_symm_apply_succ]

private lemma p3b_sl_comm {p : ℕ} {A : (Fin (p + 2) → ι) → ℝ} (hA : IsSymmT A) (a b : ι) :
    p3b_sl (p3b_sl A a) b = p3b_sl (p3b_sl A b) a := by
  funext w
  unfold p3b_sl
  have h := hA (Equiv.swap 0 1) (Fin.cons b (Fin.cons a w))
  rw [← h]
  congr 1
  funext t
  refine Fin.cases ?_ (fun t => ?_) t
  · simp
  · refine Fin.cases ?_ (fun t => ?_) t
    · simp
    · have h0 : (t.succ.succ : Fin (p + 2)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (t.succ.succ : Fin (p + 2)) ≠ 1 := by
        intro h; have := congrArg Fin.val h; simp at this
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1]
      simp

private lemma p3b_pderiv : ∀ (p : ℕ) (A : (Fin (p + 1) → ι) → ℝ) (i : ι),
    IsSymmT A → MvPolynomial.pderiv i (plainT A) =
      MvPolynomial.C ((p + 1 : ℕ) : ℝ) * plainT (p3b_sl A i) := by
  intro p
  induction p with
  | zero =>
    intro A i _
    rw [p3b_peel]
    simp only [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, p3b_zero,
      MvPolynomial.pderiv_C, smul_zero, zero_add, smul_eq_mul]
    simp [Pi.single_apply]
  | succ p ih =>
    intro A i hA
    rw [p3b_peel]
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, MvPolynomial.pderiv_X]
    rw [Finset.sum_add_distrib]
    have h2 : ∑ a, MvPolynomial.X a * MvPolynomial.pderiv i (plainT (p3b_sl A a)) =
        MvPolynomial.C ((p + 1 : ℕ) : ℝ) * plainT (p3b_sl A i) := by
      simp_rw [ih _ i (p3b_sl_symm hA _)]
      rw [p3b_peel (p3b_sl A i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [p3b_sl_comm hA a i]
      ring
    rw [h2]
    have h1 : ∑ x, plainT (p3b_sl A x) * (Pi.single (M := fun _ => MvPolynomial ι ℝ) i 1 x) =
        plainT (p3b_sl A i) := by
      simp [Pi.single_apply]
    rw [h1]
    push_cast
    simp only [map_add, map_one]
    ring

private lemma p3b_sum {κ : Type*} {m : ℕ} (S : Finset κ) (f : κ → (Fin m → ι) → ℝ) :
    plainT (fun w => ∑ a ∈ S, f a w) = ∑ a ∈ S, plainT (f a) := by
  unfold plainT
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_sum, Finset.sum_mul]

private def p3b_tr1 {p : ℕ} (B : (Fin (p + 2) → ι) → ℝ) : (Fin p → ι) → ℝ :=
  fun w => ∑ a, B (Fin.cons a (Fin.cons a w))

private lemma p3b_lap2 {p : ℕ} (B : (Fin (p + 2) → ι) → ℝ) (hB : IsSymmT B) :
    lapP (plainT B) = MvPolynomial.C (((p + 2 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
      plainT (p3b_tr1 B) := by
  unfold lapP
  have h (a : ι) : MvPolynomial.pderiv a (MvPolynomial.pderiv a (plainT B)) =
      MvPolynomial.C (((p + 2 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) *
        plainT (p3b_sl (p3b_sl B a) a) := by
    rw [p3b_pderiv (p + 1) B a hB, MvPolynomial.pderiv_C_mul,
      p3b_pderiv p (p3b_sl B a) a (p3b_sl_symm hB a), map_mul]
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, ← p3b_sum]
  rfl

private lemma p3b_lap_low {m : ℕ} (hm : m ≤ 1) (B : (Fin m → ι) → ℝ) (hB : IsSymmT B) :
    lapP (plainT B) = 0 := by
  unfold lapP
  apply Finset.sum_eq_zero
  intro a _
  interval_cases m
  · rw [p3b_zero, MvPolynomial.pderiv_C, map_zero]
  · rw [p3b_pderiv 0 B a hB, MvPolynomial.pderiv_C_mul, p3b_zero, MvPolynomial.pderiv_C,
      mul_zero]

private def p3b_cast {m m' : ℕ} (h : m = m') (A : (Fin m → ι) → ℝ) : (Fin m' → ι) → ℝ :=
  fun w => A (fun t => w (Fin.cast h t))

private lemma p3b_cast_plainT {m m' : ℕ} (h : m = m') (A : (Fin m → ι) → ℝ) :
    plainT (p3b_cast h A) = plainT A := by
  subst h; rfl

private lemma p3b_cast_symm {m m' : ℕ} (h : m = m') (A : (Fin m → ι) → ℝ) (hA : IsSymmT A) :
    IsSymmT (p3b_cast h A) := by
  subst h; exact hA

private lemma p3b_tr1_symm {p : ℕ} (B : (Fin (p + 2) → ι) → ℝ) (hB : IsSymmT B) :
    IsSymmT (p3b_tr1 B) := by
  intro σ w
  unfold p3b_tr1
  apply Finset.sum_congr rfl
  intro a _
  exact p3b_sl_symm (p3b_sl_symm hB a) a σ w

private lemma p3b_trL_zero {s : ℕ} (W : (Fin s → ι) → ℝ) :
    trL 0 W = W := by
  funext w
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

private lemma p3b_trL_succ {s i : ℕ} (W : (Fin s → ι) → ℝ) (h : s - 2 * i = s - 2 * (i + 1) + 2) :
    trL (i + 1) W = p3b_tr1 (p3b_cast h (trL i W)) := by
  funext w
  simp only [trL, p3b_tr1, p3b_cast]
  rw [← (Fin.snocEquiv (fun _ : Fin (i + 1) => ι)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  funext t
  simp only [glue, Fin.snocEquiv_apply]
  by_cases h1 : t.1 < 2 * i
  · have h2 : t.1 < 2 * (i + 1) := by omega
    rw [dif_pos h2, dif_pos h1]
    have : t.1 / 2 < i := by omega
    simp [Fin.snoc, this]
  · by_cases h2 : t.1 < 2 * (i + 1)
    · rw [dif_pos h2, dif_neg h1]
      have h3 : t.1 / 2 = i := by omega
      have h4 : ¬ (t.1 / 2 < i) := by omega
      simp only [Fin.snoc, h4, dite_false, cast_eq]
      rcases (show t.1 = 2 * i ∨ t.1 = 2 * i + 1 by omega) with ht | ht
      · have he : Fin.cast h ⟨t.1 - 2 * i, by omega⟩ = 0 := Fin.ext (by simp; omega)
        rw [he, Fin.cons_zero]
      · have he : Fin.cast h ⟨t.1 - 2 * i, by omega⟩ = (0 : Fin (s - 2 * (i + 1) + 1)).succ :=
          Fin.ext (by simp; omega)
        rw [he, Fin.cons_succ, Fin.cons_zero]
    · rw [dif_neg h2, dif_neg h1]
      have he : Fin.cast h ⟨t.1 - 2 * i, by omega⟩ =
          (⟨t.1 - 2 * (i + 1), by omega⟩ : Fin (s - 2 * (i + 1))).succ.succ :=
        Fin.ext (by simp; omega)
      rw [he, Fin.cons_succ, Fin.cons_succ]

private lemma p3b_trL_symm {s : ℕ} (W : (Fin s → ι) → ℝ) (hW : IsSymmT W) :
    ∀ i, 2 * i ≤ s → IsSymmT (trL i W)
  | 0, _ => by rw [p3b_trL_zero]; exact hW
  | i + 1, hi => by
    have h : s - 2 * i = s - 2 * (i + 1) + 2 := by omega
    rw [p3b_trL_succ W h]
    exact p3b_tr1_symm _ (p3b_cast_symm h _ (p3b_trL_symm W hW i (by omega)))

private lemma p3b_lap_trL {s : ℕ} (W : (Fin s → ι) → ℝ) (hW : IsSymmT W) (i : ℕ)
    (hi : 2 * i ≤ s) :
    lapP (plainT (trL i W)) =
      MvPolynomial.C (((s - 2 * i : ℕ) : ℝ) * ((s - 2 * i - 1 : ℕ) : ℝ)) *
        plainT (trL (i + 1) W) := by
  by_cases h2 : 2 * (i + 1) ≤ s
  · have h : s - 2 * i = s - 2 * (i + 1) + 2 := by omega
    rw [← p3b_cast_plainT h (trL i W),
      p3b_lap2 _ (p3b_cast_symm h _ (p3b_trL_symm W hW i hi)), ← p3b_trL_succ W h]
    congr 3
    · rw [h]
    · congr 1; omega
  · rw [p3b_lap_low (by omega) _ (p3b_trL_symm W hW i hi)]
    have hz : (s - 2 * i) * (s - 2 * i - 1) = 0 := by
      rcases (show s - 2 * i = 0 ∨ s - 2 * i = 1 by omega) with h | h <;> simp [h]
    have hz' : ((s - 2 * i : ℕ) : ℝ) * ((s - 2 * i - 1 : ℕ) : ℝ) = 0 := by
      exact_mod_cast hz
    rw [hz', map_zero, zero_mul]

private lemma p3b_lap_mul (f g : MvPolynomial ι ℝ) :
    lapP (f * g) = f * lapP g + g * lapP f +
      2 * ∑ a, MvPolynomial.pderiv a f * MvPolynomial.pderiv a g := by
  unfold lapP
  simp only [MvPolynomial.pderiv_mul, map_add]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma p3b_pderiv_sqN (a : ι) :
    MvPolynomial.pderiv a (sqN : MvPolynomial ι ℝ) = 2 * MvPolynomial.X a := by
  unfold sqN
  simp only [map_sum, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X, Pi.single_apply]
  simp

private lemma p3b_sqN_homog : (sqN : MvPolynomial ι ℝ).IsHomogeneous 2 := by
  unfold sqN
  apply MvPolynomial.IsHomogeneous.sum
  intro a _
  exact MvPolynomial.isHomogeneous_X_pow a 2

private lemma p3b_euler {q : MvPolynomial ι ℝ} {m : ℕ} (hq : q.IsHomogeneous m) :
    ∑ a, MvPolynomial.X a * MvPolynomial.pderiv a q = (m : MvPolynomial ι ℝ) * q := by
  rw [hq.sum_X_mul_pderiv, nsmul_eq_mul]

private lemma p3b_pderiv_const (a : ι) (c : ℝ) :
    MvPolynomial.pderiv a (MvPolynomial.C c : MvPolynomial ι ℝ) = 0 := MvPolynomial.pderiv_C

private lemma p3b_pderiv_two (a : ι) :
    MvPolynomial.pderiv a (2 : MvPolynomial ι ℝ) = 0 := by
  rw [show (2 : MvPolynomial ι ℝ) = MvPolynomial.C 2 from (map_ofNat MvPolynomial.C 2).symm]
  exact MvPolynomial.pderiv_C

private lemma p3b_pderiv_natadd (a : ι) (i : ℕ) :
    MvPolynomial.pderiv a ((i : MvPolynomial ι ℝ) + 1) = 0 := by
  rw [show ((i : MvPolynomial ι ℝ) + 1) = MvPolynomial.C ((i : ℝ) + 1) by
    rw [map_add, map_natCast, map_one]]
  exact MvPolynomial.pderiv_C

private lemma p3b_lap_sqN_pow (i : ℕ) :
    lapP ((sqN : MvPolynomial ι ℝ) ^ (i + 1)) =
      (2 * ((i : MvPolynomial ι ℝ) + 1) * ((Fintype.card ι : MvPolynomial ι ℝ) +
        2 * (i : MvPolynomial ι ℝ))) * sqN ^ i := by
  unfold lapP
  have h (a : ι) : MvPolynomial.pderiv a (MvPolynomial.pderiv a ((sqN : MvPolynomial ι ℝ) ^ (i + 1))) =
      ((i : MvPolynomial ι ℝ) + 1) * (2 * (MvPolynomial.X a * MvPolynomial.pderiv a (sqN ^ i)) +
        2 * sqN ^ i) := by
    rw [MvPolynomial.pderiv_pow, p3b_pderiv_sqN]
    simp only [Nat.add_sub_cancel, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      Pi.single_apply, if_pos rfl]
    push_cast
    rw [p3b_pderiv_natadd, p3b_pderiv_two]
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    p3b_euler (p3b_sqN_homog.pow i)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

private lemma p3b_lap_sqN_mul (i : ℕ) {q : MvPolynomial ι ℝ} {m : ℕ} (hq : q.IsHomogeneous m) :
    lapP ((sqN : MvPolynomial ι ℝ) ^ (i + 1) * q) =
      sqN ^ (i + 1) * lapP q +
        (2 * ((i : MvPolynomial ι ℝ) + 1) *
          ((Fintype.card ι : MvPolynomial ι ℝ) + 2 * (m : MvPolynomial ι ℝ) +
            2 * (i : MvPolynomial ι ℝ))) * sqN ^ i * q := by
  rw [p3b_lap_mul, p3b_lap_sqN_pow]
  have h (a : ι) : MvPolynomial.pderiv a ((sqN : MvPolynomial ι ℝ) ^ (i + 1)) *
      MvPolynomial.pderiv a q =
      (2 * ((i : MvPolynomial ι ℝ) + 1) * sqN ^ i) * (MvPolynomial.X a * MvPolynomial.pderiv a q) := by
    rw [MvPolynomial.pderiv_pow, p3b_pderiv_sqN]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, p3b_euler hq]
  ring

private lemma p3b_lap_add (f g : MvPolynomial ι ℝ) : lapP (f + g) = lapP f + lapP g := by
  unfold lapP; simp only [map_add, Finset.sum_add_distrib]

private lemma p3b_lap_sum {κ : Type*} (S : Finset κ) (f : κ → MvPolynomial ι ℝ) :
    lapP (∑ a ∈ S, f a) = ∑ a ∈ S, lapP (f a) := by
  unfold lapP; simp only [map_sum]; rw [Finset.sum_comm]

private lemma p3b_lap_C_mul (c : ℝ) (f : MvPolynomial ι ℝ) :
    lapP (MvPolynomial.C c * f) = MvPolynomial.C c * lapP f := by
  unfold lapP; simp only [MvPolynomial.pderiv_C_mul, Finset.mul_sum]

private lemma p3b_plainT_homog {m : ℕ} (A : (Fin m → ι) → ℝ) : (plainT A).IsHomogeneous m := by
  unfold plainT
  apply MvPolynomial.IsHomogeneous.sum
  intro w _
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun t => (MvPolynomial.X (w t) :
    MvPolynomial ι ℝ)) (fun _ => 1) (fun t _ => MvPolynomial.isHomogeneous_X ℝ (w t))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  simpa using h.C_mul (A w)

end p3b

private lemma hPoly_homog {s : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ) : (hPoly W).IsHomogeneous s := by
  unfold hPoly
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hi' : 2 * i ≤ s := by
    have := Finset.mem_range.mp hi; omega
  have h := ((MvPolynomial.isHomogeneous_C _ (muQ n d s i : ℝ)).mul
    (p3b_sqN_homog.pow i)).mul (p3b_plainT_homog (trL i W))
  convert h using 1
  omega

private lemma hPoly_split {s : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ) :
    ∃ r : MvPolynomial (CoefIdxD n d) ℝ, (r = 0 ∨ (2 ≤ s ∧ r.IsHomogeneous (s - 2))) ∧
      hPoly W = plainT W + sqN * r := by
  refine ⟨∑ i ∈ Finset.range (s / 2), MvPolynomial.C (muQ n d s (i + 1) : ℝ) * sqN ^ i *
    plainT (trL (i + 1) W), ?_, ?_⟩
  · by_cases hs : 2 ≤ s
    · right
      refine ⟨hs, ?_⟩
      apply MvPolynomial.IsHomogeneous.sum
      intro i hi
      have hi' : 2 * (i + 1) ≤ s := by
        have := Finset.mem_range.mp hi; omega
      have h := ((MvPolynomial.isHomogeneous_C _ (muQ n d s (i + 1) : ℝ)).mul
        (p3b_sqN_homog.pow i)).mul (p3b_plainT_homog (trL (i + 1) W))
      convert h using 1
      omega
    · left
      have : s / 2 = 0 := by omega
      rw [this, Finset.sum_range_zero]
  · unfold hPoly
    rw [Finset.sum_range_succ', Finset.mul_sum]
    have h0 : (muQ n d s 0 : ℝ) = 1 := by
      simp [muQ, cQ, Nat.factorial_ne_zero]
    rw [h0, map_one, pow_zero, one_mul, one_mul, p3b_trL_zero, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

private lemma hPoly_harmonic (hn : 1 ≤ n) {s : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ) (hW : IsSymmT W) :
    lapP (hPoly W) = 0 := by
  classical
  set L := s / 2 with hL
  let P : ℕ → MvPolynomial (CoefIdxD n d) ℝ := fun i => plainT (trL i W)
  let c : ℕ → ℝ := fun i => ((s - 2 * i : ℕ) : ℝ) * ((s - 2 * i - 1 : ℕ) : ℝ)
  let K : ℕ → ℝ := fun j => 2 * ((j : ℝ) + 1) *
    ((Fintype.card (CoefIdxD n d) : ℝ) + 2 * ((s - 2 * (j + 1) : ℕ) : ℝ) + 2 * (j : ℝ))
  let a : ℕ → MvPolynomial (CoefIdxD n d) ℝ := fun i =>
    MvPolynomial.C ((muQ n d s i : ℝ) * c i) * sqN ^ i * P (i + 1)
  let b : ℕ → MvPolynomial (CoefIdxD n d) ℝ := fun j =>
    MvPolynomial.C ((muQ n d s (j + 1) : ℝ) * K j) * sqN ^ j * P (j + 1)
  have hlap0 : lapP (MvPolynomial.C (muQ n d s 0 : ℝ) * sqN ^ 0 * P 0) = a 0 := by
    rw [pow_zero, mul_one, p3b_lap_C_mul, p3b_lap_trL W hW 0 (by omega)]
    simp only [a, c, map_mul, pow_zero, mul_one, P]
    ring
  have hlapS (j : ℕ) (hj : j + 1 ≤ L) :
      lapP (MvPolynomial.C (muQ n d s (j + 1) : ℝ) * sqN ^ (j + 1) * P (j + 1)) = a (j + 1) + b j := by
    have hj' : 2 * (j + 1) ≤ s := by omega
    rw [mul_assoc, p3b_lap_C_mul, p3b_lap_sqN_mul j (p3b_plainT_homog (trL (j + 1) W)),
      p3b_lap_trL W hW (j + 1) hj']
    simp only [a, b, c, K, P, map_mul, map_add, map_natCast, map_ofNat, map_one]
    ring
  have hterm (j : ℕ) (hj : j < L) : a j + b j = 0 := by
    have hj' : 2 * (j + 1) ≤ s := by omega
    have hm := muQ_step (d := d) hn s j hj'
    have hreal : (muQ n d s j : ℝ) * c j + (muQ n d s (j + 1) : ℝ) * K j = 0 := by
      have hm' := congrArg (fun q : ℚ => (q : ℝ)) hm
      push_cast [DQ] at hm'
      have hc : ((s - 2 * (j + 1) : ℕ) : ℝ) = (s : ℝ) - 2 * j - 2 := by
        rw [Nat.cast_sub hj']; push_cast; ring
      simp only [c, K, hc]
      linear_combination hm'
    simp only [a, b]
    rw [← add_mul, ← add_mul, ← map_add, hreal, map_zero, zero_mul, zero_mul]
  have haL : a L = 0 := by
    have hz : c L = 0 := by
      simp only [c]
      rcases (show s - 2 * L = 0 ∨ s - 2 * L = 1 by omega) with h | h <;> simp [h]
    simp only [a, hz, mul_zero, map_zero, zero_mul]
  unfold hPoly
  rw [← hL, p3b_lap_sum, Finset.sum_range_succ']
  change ∑ j ∈ Finset.range L, lapP (MvPolynomial.C (muQ n d s (j + 1) : ℝ) * sqN ^ (j + 1) *
      P (j + 1)) + lapP (MvPolynomial.C (muQ n d s 0 : ℝ) * sqN ^ 0 * P 0) = 0
  rw [Finset.sum_congr rfl (fun j hj => hlapS j (by have := Finset.mem_range.mp hj; omega)),
    hlap0, Finset.sum_add_distrib]
  have hA : ∑ j ∈ Finset.range L, a (j + 1) + a 0 = ∑ j ∈ Finset.range L, a j + a L := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ]
  calc _ = (∑ j ∈ Finset.range L, a (j + 1) + a 0) + ∑ j ∈ Finset.range L, b j := by ring
    _ = ∑ j ∈ Finset.range L, (a j + b j) + a L := by rw [hA, Finset.sum_add_distrib]; ring
    _ = 0 := by
      rw [Finset.sum_eq_zero (fun j hj => hterm j (Finset.mem_range.mp hj)), haL, add_zero]

/-! ## Assembly -/

private lemma p4_eval_plainT {ι : Type*} [Fintype ι] {m : ℕ} (A : (Fin m → ι) → ℝ) (Z : ι → ℝ) :
    MvPolynomial.eval Z (plainT A) = contr A (fun _ => Z) := by
  simp [plainT, contr, map_sum, MvPolynomial.eval_prod]

private lemma p4_eval_hPoly {s : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ) (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval Z (hPoly W) = ∑ i ∈ Finset.range (s / 2 + 1),
      (muQ n d s i : ℝ) * (∑ a, Z a ^ 2) ^ i * contr (trL i W) (fun _ => Z) := by
  simp [hPoly, sqN, map_sum, p4_eval_plainT]

private lemma p4_hPoly_sphere {s : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ) (M : CoefIdxD n d → ℝ)
    (hM : ∑ a, M a ^ 2 = 1) : MvPolynomial.eval M (hPoly W) = hS W M := by
  rw [p4_eval_hPoly, hM]
  simp [hS]

private lemma p4_contr_smul {ι : Type*} [Fintype ι] {m : ℕ} (A : (Fin m → ι) → ℝ) (c : ℝ)
    (Z : ι → ℝ) : contr A (fun _ => c • Z) = c ^ m * contr A (fun _ => Z) := by
  simp only [contr, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

private lemma p4_hPoly_smul {s : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ) (c : ℝ)
    (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval (c • Z) (hPoly W) = c ^ s * MvPolynomial.eval Z (hPoly W) := by
  rw [p4_eval_hPoly, p4_eval_hPoly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [p4_contr_smul]
  have hsq : (∑ a, (c • Z) a ^ 2) = c ^ 2 * ∑ a, Z a ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hsq, mul_pow, ← pow_mul]
  have hc : c ^ s = c ^ (2 * i) * c ^ (s - 2 * i) := by
    rw [← pow_add]; congr 1; omega
  rw [hc]
  ring

private lemma p4_unit_integrable (p : MvPolynomial (CoefIdxD n d) ℝ) :
    Integrable (fun Z => MvPolynomial.eval (unitOfD Z) p) (stdGauss (CoefIdxD n d)) := by
  let boxM := Set.Icc (fun _ : CoefIdxD n d => (-1 : ℝ)) (fun _ => 1)
  obtain ⟨G, hG⟩ := (isCompact_Icc : IsCompact boxM).bddAbove_image
    (MvPolynomial.continuous_eval p).norm.continuousOn
  apply Integrable.of_bound
    (((MvPolynomial.continuous_eval p).measurable.comp measurable_unit).aestronglyMeasurable)
    (max G 0)
  apply ae_of_all
  intro Z
  exact (hG (Set.mem_image_of_mem _ (unit_in_box Z))).trans (le_max_left G 0)

private lemma p4_nonzero_ae (hn : 1 ≤ n) :
    ∀ᵐ Z ∂stdGauss (CoefIdxD n d), Z ≠ 0 := by
  haveI : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
  haveI : ∀ _ : CoefIdxD n d, NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    fun _ => ProbabilityTheory.nullSingletonClass_gaussianReal one_ne_zero
  unfold stdGauss
  exact compl_mem_ae_iff.mpr (measure_singleton 0)


/-- One pair `(s, t)` of harmonic pieces under the normalized Gaussian. -/
private lemma p4_pair (hn : 1 ≤ n) {s t : ℕ} (W : (Fin s → CoefIdxD n d) → ℝ)
    (V : (Fin t → CoefIdxD n d) → ℝ) :
    (∫ Z, MvPolynomial.eval (unitOfD Z) (hPoly W) * MvPolynomial.eval (unitOfD Z) (hPoly V)
        ∂stdGauss (CoefIdxD n d)) *
      ∫ Z, Real.sqrt (∑ i, Z i ^ 2) ^ (s + t) ∂stdGauss (CoefIdxD n d) =
      gaussianExpectation (hPoly W * hPoly V) := by
  haveI : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
  have h := p1_gauss_polar (s + t)
    (fun Z => MvPolynomial.eval Z (hPoly W) * MvPolynomial.eval Z (hPoly V)) (by
      intro c hc Z
      rw [p4_hPoly_smul, p4_hPoly_smul]
      ring)
  refine Eq.trans h.symm ?_
  simp only [gaussianExpectation, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.eval_mul]

/-- **Lemma E for every law on the sphere.** -/
theorem errE43 (hn : 1 ≤ n) (hd : 1 ≤ d) {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (k : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) :
    Integrable (fun Z => (BofQ μ k f0 T (unitOfD Z) - gTCR μ k K f0 T (unitOfD Z)) ^ 2)
      (stdGauss (CoefIdxD n d)) ∧
    ∫ Z, (BofQ μ k f0 T (unitOfD Z) - gTCR μ k K f0 T (unitOfD Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
      ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * WfrobSqR μ k s K T / rhoD (DD n d) s := by
  refine ⟨error_integrable hn hμ k K f0 T, ?_⟩
  classical
  haveI : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
  let q : ℕ → (CoefIdxD n d → ℝ) → ℝ := fun s Z =>
    MvPolynomial.eval (unitOfD Z) (hPoly (Wt μ k s K T))
  have hae : (fun Z => (BofQ μ k f0 T (unitOfD Z) - gTCR μ k K f0 T (unitOfD Z)) ^ 2)
      =ᵐ[stdGauss (CoefIdxD n d)] fun Z => ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 k,
        q s Z * q t Z := by
    filter_upwards [p4_nonzero_ae (d := d) hn] with Z hZ
    rw [p4_error_levels hn hμ, p4_regroup, sq, Finset.sum_mul_sum]
    have hM := BstLean.Part36.unitD_sq Z hZ
    simp only [q, p4_hPoly_sphere _ _ hM]
  rw [integral_congr_ae hae]
  have hint (s t : ℕ) : Integrable (fun Z => q s Z * q t Z) (stdGauss (CoefIdxD n d)) := by
    have h := p4_unit_integrable (hPoly (Wt μ k s K T) * hPoly (Wt μ k t K T))
    simpa only [MvPolynomial.eval_mul] using h
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun t _ => hint s t))]
  apply Finset.sum_le_sum
  intro s hs
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  rw [integral_finsetSum _ (fun t _ => hint s t)]
  rw [Finset.sum_eq_single s]
  · -- the diagonal term
    have hp := p4_pair hn (Wt μ k s K T) (Wt μ k s K T)
    rw [show s + s = 2 * s by ring, p1_gauss_norm_moment] at hp
    have hρ : rhoD (Fintype.card (CoefIdxD n d) : ℝ) s = rhoD (DD n d) s := rfl
    rw [hρ] at hp
    have hρpos := rho_pos (d := d) hn s
    obtain ⟨r, hr, hsplit⟩ := hPoly_split (Wt μ k s K T)
    have hb := harmonic_sq_le (hPoly (Wt μ k s K T)) s (hPoly_homog _)
      (hPoly_harmonic hn _ (p4_Wt_symm k s hs1 K T hT)) (Wt μ k s K T) r hr hsplit
    rw [p4_frob_Wt, sq] at hb
    rw [le_div_iff₀ hρpos]
    change (∫ Z, q s Z * q s Z ∂stdGauss (CoefIdxD n d)) * rhoD (DD n d) s ≤ _
    rw [hp]
    exact hb
  · intro t ht hts
    have hp := p4_pair hn (Wt μ k s K T) (Wt μ k t K T)
    rw [harmonic_orth _ _ s t (hPoly_homog _) (hPoly_homog _)
      (hPoly_harmonic hn _ (p4_Wt_symm k s hs1 K T hT))
      (hPoly_harmonic hn _ (p4_Wt_symm k t (Finset.mem_Icc.mp ht).1 K T hT))
      (Ne.symm hts)] at hp
    exact (mul_eq_zero.mp hp).resolve_right (p1_gauss_norm_pos _).ne'
  · intro h
    exact absurd hs h

/-- **Lemma T** for every law, with a general `τ`. -/
theorem errT43 (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (T : Tens n) (ε τ : ℝ) (hτ : 0 ≤ τ)
    (hR : ∀ jl ∈ levels k, frob (fun w : Fin (jl.1 - 2 * jl.2) → Mono n d => RR μ (K jl.1 jl.2) jl.2 w) ≤
      τ * epsS ε * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 / (n : ℝ) ^ (k - (jl.1 - 2 * jl.2))) :
    ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * WfrobSqR μ k s K T / rhoD (DD n d) s ≤
      Lk k * τ * epsS ε * Nn n d k T := by
  classical
  have hf {ι : Type} [Fintype ι] {j : ℕ} (A : (Fin j → ι) → ℝ) :
      0 ≤ frob A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let F : ℕ → ℕ → ℝ := fun j l =>
    ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l *
      aSq n d T j l / (n : ℝ) ^ (k - (j - 2 * l))
  have hlevel (s : ℕ) (hs : s ∈ Finset.Icc 1 k)
      (l : ℕ) (hl : l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k)) :
      (s.factorial : ℝ) * ((kapQ n d (s + 2 * l) l : ℝ) ^ 2 *
        frob (trL l (T (s + 2 * l))) *
        frob (fun w : Fin (s + 2 * l - 2 * l) → Mono n d =>
          (RR μ (K (s + 2 * l) l) l w : ℝ))) / rhoD (DD n d) s ≤
      τ * epsS ε * F (s + 2 * l) l := by
    have hsl : (s + 2 * l, l) ∈ levels k := by
      simp only [Finset.mem_Icc] at hs
      simp only [Finset.mem_filter, Finset.mem_range] at hl
      simp only [levels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range]
      omega
    have he : s + 2 * l - 2 * l = s := by omega
    have hres := hR (s + 2 * l, l) hsl
    dsimp only at hres
    have hc : 0 ≤ (cQ (s + 2 * l) l : ℝ) ^ 2 / DD n d ^ (s + 2 * l) :=
      div_nonneg (sq_nonneg _) (pow_nonneg (dimension_pos hn).le _)
    have hfac : 0 ≤ (s.factorial : ℝ) * frob (trL l (T (s + 2 * l))) :=
      mul_nonneg (Nat.cast_nonneg _) (hf _)
    calc
      _ = ((s.factorial : ℝ) * frob (trL l (T (s + 2 * l)))) *
          ((kapQ n d (s + 2 * l) l : ℝ) ^ 2 / rhoD (DD n d) s) *
          frob (fun w : Fin (s + 2 * l - 2 * l) → Mono n d =>
            (RR μ (K (s + 2 * l) l) l w : ℝ)) := by ring
      _ ≤ ((s.factorial : ℝ) * frob (trL l (T (s + 2 * l)))) *
          ((cQ (s + 2 * l) l : ℝ) ^ 2 / DD n d ^ (s + 2 * l)) *
          (τ * epsS ε * (s + 2 * l - 2 * l : ℕ) * 4 ^ l /
            (n : ℝ) ^ (k - (s + 2 * l - 2 * l))) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (kap_bound hn s l) hfac)
          hres (hf _) (mul_nonneg hfac hc)
      _ = _ := by dsimp [F, aSq]; simp only [he]; ring
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 k, (Lk k : ℝ) *
        ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
          (s.factorial : ℝ) * ((kapQ n d (s + 2 * l) l : ℝ) ^ 2 *
            frob (trL l (T (s + 2 * l))) *
            frob (fun w : Fin (s + 2 * l - 2 * l) → Mono n d =>
              (RR μ (K (s + 2 * l) l) l w : ℝ))) / rhoD (DD n d) s := by
      apply Finset.sum_le_sum
      intro s hs
      have h := W_bound (μ := μ) k s (Finset.mem_Icc.mp hs).1 K T
      calc
        _ ≤ (s.factorial : ℝ) * ((Lk k : ℝ) *
          ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
            (kapQ n d (s + 2 * l) l : ℝ) ^ 2 * frob (trL l (T (s + 2 * l))) *
              frob (fun w : Fin (s + 2 * l - 2 * l) → Mono n d =>
                (RR μ (K (s + 2 * l) l) l w : ℝ))) / rhoD (DD n d) s :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
            (rho_pos hn s).le
        _ = _ := by
          simp_rw [Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ ≤ ∑ s ∈ Finset.Icc 1 k, (Lk k : ℝ) *
        ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
          τ * epsS ε * F (s + 2 * l) l := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun l hl => hlevel s hs l hl)
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [regroup_levels]
      change (Lk k : ℝ) * (τ * epsS ε * Nn n d k T) = _
      ring

end BstLean.Part43

