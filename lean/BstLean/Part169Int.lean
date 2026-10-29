import BstLean.Part169Asm

/-!
# Part 169 (file `Int`): the integrability items of `MomIn` hold for every retained value

No proof is left open; no `native_decide` or `axiom` is used.

Every function in `MomIn` is bounded in the index `a` (for each fixed retained value `c`):
`f̄`, `ω̄`, `S̄` by the Frobenius norms of `A₁`, `A₂` (`|x_s(v)| ≤ 1`), and `f̃`, `ω̃` because the
node index takes fewer than `J_s` values. So the integrability items are theorems, not
hypotheses.

* `bdd_fbR`, `bdd_wbR`, `bdd_Sb`, `bdd_ftR`, `bdd_wtR`, `bdd_VR`: the bounds.
* `MomB c ε v_max a_ω a_f H_f C_v`: `MomIn` without the integrability items.
* **`momIn_of_momB`**: `MomB → MomIn`, for every `c`.
* **`classifier_paper_momB80k`**: the end theorem with `MomB` in place of `MomIn`.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

lemma bdd_fX (hn : 1 ≤ n) (c : Ret n) {x : Fin n → ℝ} (hx : normSq x ≤ 1) :
    |fX c x| ≤ √(BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) / √(n : ℝ) := by
  have h := fX_sub_le hn c x 0
  have e : fX c 0 = 0 := by unfold fX; rw [hid2_zero']; simp
  rw [e, sub_zero, hid2_zero', sub_zero] at h
  refine h.trans (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
  refine (BstLean.Part131.normSq_hid2_le _ _ _).trans ?_
  have h1 := BstLean.Part131.frob_nonneg (A1 c)
  have h2 := BstLean.Part131.frob_nonneg (A2 c)
  calc BstLean.Part131.frob (A2 c) * (BstLean.Part131.frob (A1 c) * normSq x)
      ≤ BstLean.Part131.frob (A2 c) * (BstLean.Part131.frob (A1 c) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx h1) h2
    _ = _ := by ring

lemma bdd_wX (c : Ret n) {x : Fin n → ℝ} (hx : normSq x ≤ 1) :
    |wX c x| ≤ BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) / n := by
  unfold wX
  rw [abs_of_nonneg (div_nonneg (normSq_nonneg _) (Nat.cast_nonneg _))]
  refine div_le_div_of_nonneg_right ((BstLean.Part131.normSq_hid2_le _ _ _).trans ?_)
    (Nat.cast_nonneg _)
  have h1 := BstLean.Part131.frob_nonneg (A1 c)
  have h2 := BstLean.Part131.frob_nonneg (A2 c)
  calc BstLean.Part131.frob (A2 c) * (BstLean.Part131.frob (A1 c) * normSq x)
      ≤ BstLean.Part131.frob (A2 c) * (BstLean.Part131.frob (A1 c) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx h1) h2
    _ = _ := by ring

lemma abs_int_le {F : (Fin (n - 1) → ℝ) → ℝ} {C : ℝ} (h : ∀ v, |F v| ≤ C) :
    |∫ v, F v ∂stdGauss (Fin (n - 1))| ≤ C := by
  have hb := norm_integral_le_of_norm_le_const (μ := stdGauss (Fin (n - 1))) (f := F) (C := C)
    (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact h v)
  rw [Real.norm_eq_abs] at hb
  simpa using hb

lemma bdd_fbR (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |fbR c a| ≤ M :=
  ⟨_, fun a => by
    rw [fbR_eq]; unfold fbarS
    exact abs_int_le fun v => bdd_fX hn c (normSq_xLat_le' hn c
      (BstLean.Part162.latC_sq_le _ c a) v)⟩

lemma bdd_wbR (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |wbR c a| ≤ M :=
  ⟨_, fun a => by
    rw [wbR_eq]; unfold wbarS
    exact abs_int_le fun v => bdd_wX c (normSq_xLat_le' hn c
      (BstLean.Part162.latC_sq_le _ c a) v)⟩

lemma bdd_Sb (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |(dP c).Sb a| ≤ M :=
  ⟨2 / (mA n : ℝ) * (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)), fun a => by
    show |∫ v, BstLean.Part161.sA (paperDesignP n) c a v ∂stdGauss (Fin (n - 1))| ≤ _
    refine abs_int_le fun v => ?_
    rw [abs_of_nonneg (by show 0 ≤ BstLean.Part162.sgA (paperDesignP n) c a v ^ 2; positivity)]
    exact sA_le hn _ c a v⟩

lemma gIdx_lt (c : Ret n) (hn : 1 ≤ n) (s : ℝ) : gIdx c s < Js n :=
  nodeIdx_lt (by unfold Js; omega) _ _ _

lemma bdd_ftR (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |ftR c a| ≤ M :=
  ⟨∑ g ∈ Finset.range (Js n), |fPass c (nodeS c g)|, fun a => by
    unfold ftR
    exact Finset.single_le_sum (f := fun g => |fPass c (nodeS c g)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (gIdx_lt c hn _))⟩

lemma bdd_wtR (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |wtR c a| ≤ M :=
  ⟨∑ g ∈ Finset.range (Js n), |wPass c (nodeS c g)|, fun a => by
    unfold wtR
    exact Finset.single_le_sum (f := fun g => |wPass c (nodeS c g)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (gIdx_lt c hn _))⟩

lemma bdd_VR (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |VR c a| ≤ M := by
  obtain ⟨M1, h1⟩ := bdd_wbR hn c
  obtain ⟨M2, h2⟩ := bdd_fbR hn c
  obtain ⟨M3, h3⟩ := bdd_Sb hn c
  refine ⟨M1 + M2 ^ 2 + M3 / (2 / (n : ℝ)), fun a => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold VR
  have e1 : |fbR c a ^ 2| ≤ M2 ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 a) 2
  have e2 : |(dP c).Sb a / (2 / (n : ℝ))| ≤ M3 / (2 / (n : ℝ)) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 / n)]
    exact div_le_div_of_nonneg_right (h3 a) (by positivity)
  have := abs_sub (wbR c a - fbR c a ^ 2) ((dP c).Sb a / (2 / (n : ℝ)))
  have := abs_sub (wbR c a) (fbR c a ^ 2)
  linarith [h1 a]

/-- A bounded measurable function is integrable on any set (finite measure). -/
lemma intOn_of_bdd {F : Ix n → ℝ} (mF : Measurable F) {M : ℝ} (hF : ∀ a, |F a| ≤ M)
    (K : Set (Ix n)) : IntegrableOn F K (muI n) :=
  (Integrable.mono' (integrable_const M) mF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hF a)).integrableOn

lemma bdd_pow {F : Ix n → ℝ} {M : ℝ} (hF : ∀ a, |F a| ≤ M) (k : ℕ) :
    ∀ a, |F a ^ k| ≤ M ^ k := fun a => by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hF a) k

lemma bdd_mul {F G : Ix n → ℝ} {M N : ℝ} (hF : ∀ a, |F a| ≤ M) (hG : ∀ a, |G a| ≤ N) :
    ∀ a, |F a * G a| ≤ M * N := fun a => by
  rw [abs_mul]; exact mul_le_mul (hF a) (hG a) (abs_nonneg _) ((abs_nonneg _).trans (hF a))

lemma bdd_nsub {F G : Ix n → ℝ} {M N : ℝ} (hF : ∀ a, |F a| ≤ M) (hG : ∀ a, |G a| ≤ N) :
    ∀ a, |(n : ℝ) * (F a - G a)| ≤ n * (M + N) := fun a => by
  rw [abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hF a) (hG a)))
    (Nat.cast_nonneg _)

lemma bdd_nmul {F : Ix n → ℝ} {M : ℝ} (hF : ∀ a, |F a| ≤ M) :
    ∀ a, |(n : ℝ) * F a| ≤ n * M := fun a => by
  rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left (hF a) (Nat.cast_nonneg _)

/-- **`MomIn` without the integrability items.** -/
structure MomB (c : Ret n) (ε vmax aw af Hf Cv : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  hW8 : ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8
  hF8 : ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2

/-- **The integrability items of `MomIn` are theorems.** -/
theorem momIn_of_momB (hn : 1 ≤ n) {c : Ret n} {ε vmax aw af Hf Cv : ℝ}
    (h : MomB c ε vmax aw af Hf Cv) : MomIn c ε vmax aw af Hf Cv := by
  obtain ⟨Mf, hf⟩ := bdd_fbR hn c
  obtain ⟨Mw, hw⟩ := bdd_wbR hn c
  obtain ⟨Nf, hf'⟩ := bdd_ftR hn c
  obtain ⟨Nw, hw'⟩ := bdd_wtR hn c
  obtain ⟨MV, hV⟩ := bdd_VR hn c
  have mf := measurable_fbR c
  have mw := measurable_wbR c
  have mf' := measurable_ftR c
  have mw' := measurable_wtR c
  have mV := measurable_VR c
  have mW : Measurable (fun a => (n : ℝ) * (wbR c a - wtR c a)) := (mw.sub mw').const_mul _
  have mF : Measurable (fun a => (n : ℝ) * (fbR c a - ftR c a)) := (mf.sub mf').const_mul _
  have bW := bdd_nsub hw hw'
  have bF := bdd_nsub hf hf'
  exact
  { hVm := h.hVm
    iW2 := intOn_of_bdd (mW.pow_const 2) (bdd_pow bW 2) _
    iW6 := intOn_of_bdd (mW.pow_const 6) (bdd_pow bW 6) _
    iW8 := intOn_of_bdd (mW.pow_const 8) (bdd_pow bW 8) _
    iF2 := intOn_of_bdd (mF.pow_const 2) (bdd_pow bF 2) _
    iF4 := intOn_of_bdd (mF.pow_const 4) (bdd_pow bF 4) _
    iF8 := intOn_of_bdd (mF.pow_const 8) (bdd_pow bF 8) _
    if4 := intOn_of_bdd (mf.pow_const 4) (bdd_pow hf 4) _
    if24 := intOn_of_bdd (mf.pow_const 24) (bdd_pow hf 24) _
    ifF2 := intOn_of_bdd ((mf.pow_const 2).mul (mF.pow_const 2))
      (bdd_mul (bdd_pow hf 2) (bdd_pow bF 2)) _
    ifF6 := intOn_of_bdd ((mf.pow_const 6).mul (mF.pow_const 6))
      (bdd_mul (bdd_pow hf 6) (bdd_pow bF 6)) _
    iV := intOn_of_bdd ((mV.const_mul _).pow_const 2) (bdd_pow (bdd_nmul hV) 2) _
    hW8 := h.hW8
    hF8 := h.hF8
    hf4 := h.hf4
    hf24 := h.hf24
    hV := h.hV }

/-- **The classifier theorem with the moment bounds `MomB`** (no integrability hypothesis;
every `n ≥ 80 000`). -/
theorem classifier_paper_momB80k (hn : 80000 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ BstLean.Part167.roomE)
    {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (4295 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomB c ε vmax aw af Hf Cv) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_mom80k hn t hEA hEb hA hb hroom hε1 hT haw haf hHf hCv hnum
    fun c hc => momIn_of_momB (by omega) (hM c hc)

end BstLean.Part169
