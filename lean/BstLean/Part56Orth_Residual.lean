import BstLean.Part56Orth_Projection

namespace BstLean.Part56.Orth

open BstLean.Part36 (CoefIdxD monoVal)
open BstLean.Part41 (Mono phiM colM)
open BstLean.Part53 (linZ nsq)

variable {n d : ℕ}

noncomputable def residualFeature (v x : Fin n → ℝ) : Mono n d → ℝ := fun p =>
  phiM x p - ∑ j ∈ Finset.range (d + 1), betaJ d j v x * phiB d j v p

private noncomputable def residualBlock (j : ℕ) (v x : Fin n → ℝ) (p : Mono n d) : ℝ :=
  phiB d j x p - betaJ d j v x * phiB d j v p

private lemma block_sum (x : Fin n → ℝ) (p : Mono n d) :
    (∑ j ∈ Finset.range (d + 1), phiB d j x p) = phiM x p := by
  classical
  rw [Finset.sum_eq_single (p.1 : ℕ)]
  · simp [phiB]
  · intro j hj h
    simp [phiB, Ne.symm h]
  · intro h
    exact (h (Finset.mem_range.mpr p.1.2)).elim

private lemma residualBlock_off (j : ℕ) (v x : Fin n → ℝ) (p : Mono n d)
    (h : j ≠ (p.1 : ℕ)) : residualBlock j v x p = 0 := by
  simp [residualBlock, phiB, Ne.symm h]

private lemma residualBlock_sum (v x : Fin n → ℝ) (p : Mono n d) :
    (∑ j ∈ Finset.range (d + 1), residualBlock j v x p) = residualFeature v x p := by
  classical
  simp only [residualBlock, Finset.sum_sub_distrib, block_sum, residualFeature]

private lemma residualBlock_squares (v x : Fin n → ℝ) (p : Mono n d) :
    (∑ j ∈ Finset.range (d + 1), residualBlock j v x p ^ 2) = residualFeature v x p ^ 2 := by
  classical
  rw [← residualBlock_sum]
  have hs : (∑ j ∈ Finset.range (d + 1), residualBlock j v x p) =
      residualBlock (p.1 : ℕ) v x p := by
    apply Finset.sum_eq_single (p.1 : ℕ)
    · intro j hj h
      exact residualBlock_off j v x p h
    · intro h
      exact (h (Finset.mem_range.mpr p.1.2)).elim
  rw [hs]
  apply Finset.sum_eq_single (p.1 : ℕ)
  · intro j hj h
    rw [residualBlock_off j v x p h, zero_pow (by omega)]
  · intro h
    exact (h (Finset.mem_range.mpr p.1.2)).elim

private lemma residualBlock_norm (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ)
    (j : ℕ) (hj : j ≤ d) :
    (∑ p : Mono n d, residualBlock j v x p ^ 2) =
      kJ d j x x - kJ d j x v * kJ d j x v / kJ d j v v := by
  classical
  have hzero := ne_of_gt (block_norm_pos v hv j hj)
  have he (p : Mono n d) : residualBlock j v x p ^ 2 =
      phiB d j x p ^ 2 - (2 * betaJ d j v x) * (phiB d j x p * phiB d j v p) +
        betaJ d j v x ^ 2 * phiB d j v p ^ 2 := by
    unfold residualBlock
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, pow_two]
  change kJ d j x x - (2 * betaJ d j v x) * kJ d j x v +
    (betaJ d j v x * betaJ d j v x) * kJ d j v v = _
  unfold betaJ
  field_simp
  <;> ring

private lemma zero_block_eq (x v : Fin n → ℝ) : phiB d 0 x = phiB d 0 v := by
  funext p
  unfold phiB
  split_ifs with h
  · have hp : (p.2 : Multiset (Fin n)) = 0 := Multiset.card_eq_zero.mp (p.2.2.trans h)
    simp [phiM, monoVal, hp]
  · rfl

/-- The residual feature has the frozen residual variance. -/
theorem residualFeature_norm (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    nsq (residualFeature (d := d) v x) = tauR d v x := by
  classical
  change (∑ p : Mono n d, residualFeature v x p ^ 2) = _
  simp_rw [← residualBlock_squares]
  rw [Finset.sum_comm]
  have he (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :=
    residualBlock_norm (d := d) v hv x j (by have := Finset.mem_range.mp hj; omega)
  rw [Finset.sum_congr rfl he]
  have h0 : kJ d 0 x x - kJ d 0 x v * kJ d 0 x v / kJ d 0 v v = 0 := by
    have hk : kJ d 0 x x = kJ d 0 v v := by unfold kJ; rw [zero_block_eq x v]
    have hkv : kJ d 0 x v = kJ d 0 v v := by unfold kJ; rw [zero_block_eq x v]
    rw [hk, hkv, mul_div_cancel_right₀ _ (ne_of_gt (block_norm_pos v hv 0 (by omega))), sub_self]
  have hi : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hi, Finset.sum_insert (by simp), h0, zero_add]
  rfl

/-- Evaluating the residual coefficient array equals evaluating the residual feature. -/
theorem residual_value (v x : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) :
    linZ (Z - projA v Z) (fun p : Mono n d => phiM x p) =
      linZ Z (residualFeature v x) := by
  classical
  have hm : linZ Z (fun p : Mono n d =>
      ∑ j ∈ Finset.range (d + 1), betaJ d j v x * phiB d j v p) = mux Z v x := by
    funext a
    simp only [linZ, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mux, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ancRK, linZ]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hl : linZ (Z - projA v Z) (fun p : Mono n d => phiM x p) =
      linZ Z (fun p : Mono n d => phiM x p) - mux Z v x := by
    rw [← projected_value v x Z]
    funext a
    simp [linZ, colM, sub_mul, Finset.sum_sub_distrib]
  rw [hl, ← hm]
  funext a
  simp [linZ, residualFeature, mul_sub, Finset.sum_sub_distrib]

theorem map_linear (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    BstLean.Part36.mapMD M x = linZ M (fun p : Mono n d => phiM x p) := by
  classical
  funext a
  unfold BstLean.Part36.mapMD linZ BstLean.Part36.coefD
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun i => ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then M ⟨⟨i, h⟩, (β, a)⟩ else 0) * monoVal x β.1)]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro β hβ
  simp [colM, phiM, i.2]

private lemma linZ_add (Z W : CoefIdxD n d → ℝ) (ψ : Mono n d → ℝ) :
    linZ (Z + W) ψ = linZ Z ψ + linZ W ψ := by
  classical
  funext a
  simp [linZ, colM, add_mul, Finset.sum_add_distrib]

private lemma linZ_smul (s : ℝ) (Z : CoefIdxD n d → ℝ) (ψ : Mono n d → ℝ) :
    linZ (s • Z) ψ = s • linZ Z ψ := by
  classical
  funext a
  simp [linZ, colM, mul_assoc, Finset.mul_sum]

private lemma linZ_feature_smul (s : ℝ) (Z : CoefIdxD n d → ℝ) (ψ : Mono n d → ℝ) :
    linZ Z (s • ψ) = s • linZ Z ψ := by
  classical
  funext a
  simp [linZ, mul_left_comm, Finset.mul_sum]

private lemma mux_smul (s : ℝ) (Z : CoefIdxD n d → ℝ) (v x : Fin n → ℝ) :
    mux (s • Z) v x = s • mux Z v x := by
  classical
  simp only [mux, anchor_smul, Finset.smul_sum, smul_smul, mul_comm]

/-- The resampled field is the anchor mean plus a Gaussian linear residual. -/
theorem resampled_map (s : ℝ) (v x : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ) :
    BstLean.Part36.mapMD (s • (projA v Z + (W - projA v W))) x =
      mux (s • Z) v x + linZ W (s • residualFeature v x) := by
  rw [map_linear, linZ_smul, linZ_add, projected_value, residual_value,
    smul_add, linZ_feature_smul, mux_smul]

theorem residualFeature_scaled_norm (s : ℝ) (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    nsq (s • residualFeature (d := d) v x) = s ^ 2 * tauR d v x := by
  classical
  simp only [nsq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [show (∑ p : Mono n d, residualFeature v x p ^ 2) = tauR d v x
    from residualFeature_norm v hv x]

end BstLean.Part56.Orth
