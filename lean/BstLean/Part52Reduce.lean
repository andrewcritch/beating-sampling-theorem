import BstLean.Part52Moments

/-!
# Part 52, wave 3: from `f_α = Tal k α` and `M = Z/‖Z‖` to `Xc`, `Var_μ hZ` at the raw `Z`

* `fval_Tal`: `f_α(y) = c_α ∏_t y_{ι t}` with `c_α = #{w : mset w = α} ≥ 1`, for `mset ι = α`.
* `hZ_smul`: `hZ ι (c • Z) = c^k hZ ι Z`.
* `event_of_raw`: for `Z ≠ 0`, `ε² Var_μ hZ(Z) < Xc(Z)²` implies the event of Lemma P at `Z`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part52

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD mapMD monoVal)
open BstLean.Part41 (Mono phiM phiSq varU mset contr fval Tens)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part40 (SphLaw)

variable {n d k : ℕ}

theorem prod_word (y : Fin n → ℝ) {j : ℕ} (w : Fin j → Fin n) :
    ∏ t, y (w t) = ((mset w).map y).prod := by
  unfold mset
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

theorem fval_Tal (hk : 1 ≤ k) (α : Multiset (Fin n)) (ι : Fin k → Fin n) (hι : mset ι = α)
    (y : Fin n → ℝ) :
    fval k 0 (Tal k α) y =
      ((Finset.univ.filter fun w : Fin k → Fin n => mset w = α).card : ℝ) * ∏ t, y (ι t) := by
  classical
  unfold fval
  rw [zero_add, Finset.sum_eq_single k]
  · unfold contr
    have h : ∀ w : Fin k → Fin n, Tal k α k w * ∏ t, y (w t) =
        if mset w = α then ∏ t, y (ι t) else 0 := by
      intro w
      by_cases hw : mset w = α
      · simp only [Tal, hw, and_self, if_true, one_mul]
        rw [prod_word, prod_word, hw, hι]
      · simp [Tal, hw]
    simp_rw [h]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  · intro j _ hj
    unfold contr
    apply Finset.sum_eq_zero
    intro w _
    simp [Tal, hj]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩) h

theorem cal_pos (α : Multiset (Fin n)) (ι : Fin k → Fin n) (hι : mset ι = α) :
    (0 : ℝ) < ((Finset.univ.filter fun w : Fin k → Fin n => mset w = α).card : ℝ) := by
  classical
  have : 0 < (Finset.univ.filter fun w : Fin k → Fin n => mset w = α).card :=
    Finset.card_pos.mpr ⟨ι, by simp [hι]⟩
  exact_mod_cast this

theorem mapMD_smul (c : ℝ) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (a : Fin n) :
    mapMD (c • Z) x a = c * mapMD Z x a := by
  rw [BstLean.Part49.mapMD_eq, BstLean.Part49.mapMD_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp [mul_assoc]

theorem hZ_smul (ι : Fin k → Fin n) (c : ℝ) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    hZ ι (c • Z) x = c ^ k * hZ ι Z x := by
  unfold hZ
  simp_rw [mapMD_smul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem varU_const_mul (μ : Measure (Fin n → ℝ)) (c : ℝ) (h : (Fin n → ℝ) → ℝ) :
    varU μ (fun x => c * h x) = c ^ 2 * varU μ h := by
  unfold varU
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [integral_const_mul]
  ring

theorem BofQ_Tal (hk : 1 ≤ k) (μ : Measure (Fin n → ℝ)) (α : Multiset (Fin n)) (ι : Fin k → Fin n)
    (hι : mset ι = α) (M : CoefIdxD n d → ℝ) :
    BofQ μ k 0 (Tal k α) M =
      ((Finset.univ.filter fun w : Fin k → Fin n => mset w = α).card : ℝ) * Xc μ ι M := by
  unfold BofQ Xc
  simp_rw [fval_Tal hk α ι hι]
  rw [integral_const_mul]
  rfl

theorem varFQ_Tal (hk : 1 ≤ k) (μ : Measure (Fin n → ℝ)) (α : Multiset (Fin n)) (ι : Fin k → Fin n)
    (hι : mset ι = α) (M : CoefIdxD n d → ℝ) :
    varFQ μ k 0 (Tal k α) M =
      ((Finset.univ.filter fun w : Fin k → Fin n => mset w = α).card : ℝ) ^ 2 * varU μ (hZ ι M) := by
  unfold varFQ
  simp_rw [fval_Tal hk α ι hι]
  exact varU_const_mul μ _ _

/-- For `Z ≠ 0`, `ε² Var_μ hZ(Z) < Xc(Z)²` implies the event of Lemma P at `Z`. -/
theorem event_of_raw (hk : 1 ≤ k) (μ : Measure (Fin n → ℝ)) (α : Multiset (Fin n))
    (ι : Fin k → Fin n) (hι : mset ι = α) (ε : ℝ) (Z : CoefIdxD n d → ℝ) (hZ0 : Z ≠ 0)
    (h : ε ^ 2 * varU μ (hZ ι Z) < Xc μ ι Z ^ 2) :
    ε ^ 2 * varFQ μ k 0 (Tal k α) (unitOfD Z) < BofQ μ k 0 (Tal k α) (unitOfD Z) ^ 2 := by
  rw [BofQ_Tal hk μ α ι hι, varFQ_Tal hk μ α ι hι]
  set s := 1 / Real.sqrt (∑ i, Z i ^ 2)
  have hu : unitOfD Z = s • Z := rfl
  have hX : Xc μ ι (unitOfD Z) = s ^ k * Xc μ ι Z := by
    unfold Xc; simp_rw [hu, hZ_smul]; rw [integral_const_mul]
  have hV : varU μ (hZ ι (unitOfD Z)) = (s ^ k) ^ 2 * varU μ (hZ ι Z) := by
    have : hZ ι (unitOfD Z) = fun x => s ^ k * hZ ι Z x := funext (fun x => by rw [hu, hZ_smul])
    rw [this, varU_const_mul]
  rw [hX, hV]
  set c := ((Finset.univ.filter fun w : Fin k → Fin n => mset w = α).card : ℝ)
  have hc : 0 < c := cal_pos α ι hι
  have hsum : 0 < ∑ i, Z i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, Z i ≠ 0 := by
      by_contra hc0; push Not at hc0; exact hZ0 (funext hc0)
    exact Finset.sum_pos' (fun j _ => sq_nonneg (Z j)) ⟨i, Finset.mem_univ _, by positivity⟩
  have hs0 : 0 < s := by positivity
  have hpos : 0 < (c * s ^ k) ^ 2 := by positivity
  calc ε ^ 2 * (c ^ 2 * ((s ^ k) ^ 2 * varU μ (hZ ι Z)))
        = (c * s ^ k) ^ 2 * (ε ^ 2 * varU μ (hZ ι Z)) := by ring
      _ < (c * s ^ k) ^ 2 * Xc μ ι Z ^ 2 := mul_lt_mul_of_pos_left h hpos
      _ = (c * (s ^ k * Xc μ ι Z)) ^ 2 := by ring

end BstLean.Part52
