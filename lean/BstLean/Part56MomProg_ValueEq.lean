import BstLean.Part56MomProg_Values

/-! The stage values compute the surrogate weights. -/

namespace BstLean.Part56.MomProg

open MvPolynomial
open BstLean.Part56
open BstLean.Part41 (Mono phiM)

variable {n d D : ℕ}

theorem rep_zero' {c : Idx n D → ℝ} (h : ∀ μ, c μ = 0) : Rep c 0 := by
  intro μ; simp [h μ]

theorem bind_monoPoly (a : Fin n) (v : Fin n → ℝ) (p : Mono n d) :
    bind₁ (Lform a v) (monoPoly p) = ((p.2.val.toList).map (Lform a v)).prod := by
  unfold monoPoly
  rw [map_multiset_prod, Multiset.map_map]
  conv_lhs => rw [← Multiset.coe_toList p.2.val]
  rw [Multiset.map_coe, Multiset.prod_coe]
  congr 1
  apply List.map_congr_left
  intro m _
  simp

theorem rep_img (a : Fin n) (v : Fin n → ℝ) (p : Mono n d) :
    Rep (fun μ => imgF d D (RmF a v) (p, μ)) (bind₁ (Lform a v) (monoPoly p)) := by
  rw [bind_monoPoly]
  have h := rep_plist (D := D) (fun m => linVec (fun j => RmF a v (m, j))) (Lform a v)
    (fun m => rep_lin _) (p.2.val.toList)
  intro μ
  exact h μ

theorem bind_kernel (a : Fin n) (v : Fin n → ℝ) (j : ℕ) :
    bind₁ (Lform a v) (kernelPoly d j v) =
      ∑ p : Mono n d, if (p.1 : ℕ) = j then C (phiM v p) * bind₁ (Lform a v) (monoPoly p)
        else 0 := by
  unfold kernelPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem rep_ker (a : Fin n) (v : Fin n → ℝ) (j : Fin (d + 1)) :
    Rep (fun μ => kerF d D (pvF d v) (imgF d D (RmF a v)) (j, μ))
      (bind₁ (Lform a v) (kernelPoly d j v)) := by
  rw [bind_kernel]
  apply rep_sum
  intro p _
  split_ifs with h
  · have := rep_smul (phiM v p) (rep_img (D := D) a v p)
    intro μ
    rw [← this μ]
    simp [h, pvF]
  · exact rep_zero' (fun μ => by simp [h])

theorem rep_beta (a : Fin n) (v : Fin n → ℝ) (j : Fin (d + 1)) :
    Rep (fun μ => betaF d D (kiF d v) (kerF d D (pvF d v) (imgF d D (RmF a v))) (j, μ))
      (bind₁ (Lform a v) (betaPoly d j v)) := by
  unfold betaPoly
  rw [map_mul, bind₁_C_right]
  have h := rep_smul (1 / kJ d j v v) (rep_ker (D := D) a v j)
  intro μ
  exact h μ

theorem bind_diag (a : Fin n) (v : Fin n → ℝ) (j : ℕ) :
    bind₁ (Lform a v) (diagPoly n d j) =
      ∑ p : Mono n d, if (p.1 : ℕ) = j then
        bind₁ (Lform a v) (monoPoly p) * bind₁ (Lform a v) (monoPoly p) else 0 := by
  unfold diagPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp [pow_two]

theorem rep_diag (a : Fin n) (v : Fin n → ℝ) (j : Fin (d + 1)) :
    Rep (fun μ => diagF d D (sqF d D (imgF d D (RmF a v))) (j, μ))
      (bind₁ (Lform a v) (diagPoly n d j)) := by
  rw [bind_diag]
  apply rep_sum
  intro p _
  split_ifs with h
  · have := rep_mul (rep_img (D := D) a v p) (rep_img (D := D) a v p)
    intro μ
    rw [← this μ]
    simp [h, sqF]
  · exact rep_zero' (fun μ => by simp [h])

theorem sum_Icc_fin (f : ℕ → MvPolynomial (Fin n) ℝ) :
    ∑ j ∈ Finset.Icc 1 d, f j = ∑ j : Fin (d + 1), if 1 ≤ (j : ℕ) then f j else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if 1 ≤ j then f j else 0) (d + 1),
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j; simp; omega

theorem rep_tau (a : Fin n) (v : Fin n → ℝ) :
    Rep (fun μ => tauF d D (diagF d D (sqF d D (imgF d D (RmF a v)))) (kiF d v)
        (kkF d D (kerF d D (pvF d v) (imgF d D (RmF a v)))) μ)
      (bind₁ (Lform a v) (tauPoly d v)) := by
  unfold tauPoly
  rw [map_sum, sum_Icc_fin]
  apply rep_sum
  intro j _
  split_ifs with h
  · rw [map_sub, map_mul, bind₁_C_right, map_pow, pow_two]
    have h1 := rep_diag (D := D) a v j
    have h2 := rep_smul (1 / kJ d j v v) (rep_mul (rep_ker (D := D) a v j) (rep_ker (D := D) a v j))
    have h3 := rep_sub h1 h2
    intro μ
    rw [← h3 μ]
    rfl
  · exact rep_zero' (fun μ => rfl)

theorem rep_Q (a : Fin n) (v : Fin n → ℝ) {k : ℕ} (κ : KeyRK k d) :
    let img := imgF d D (RmF a v)
    let ker := kerF d D (pvF d v) img
    Rep (fun μ => QF d D (tbF d D (diagF d D (sqF d D img)) (kiF d v) (kkF d D ker) ker) (κ, μ))
      (Qpoly a v κ) := by
  intro img ker
  let P : Option (Fin (d + 1)) → MvPolynomial (Fin n) ℝ := fun o =>
    match o with
    | none => bind₁ (Lform a v) (tauPoly d v)
    | some j => bind₁ (Lform a v) (betaPoly d j v)
  have hc : ∀ o, Rep (fun μ => tbF d D (diagF d D (sqF d D img)) (kiF d v) (kkF d D ker) ker
      (o, μ)) (P o) := by
    intro o
    cases o with
    | none => exact rep_tau a v
    | some j => exact rep_beta a v j
  have h := rep_plist _ P hc (keyList d κ)
  have hp : ((keyList d κ).map P).prod = Qpoly a v κ := by
    unfold Qpoly weightPoly keyList
    rw [map_mul, map_pow, map_prod, List.map_append, List.prod_append, List.map_replicate,
      List.prod_replicate, List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hp] at h
  exact h

theorem fullF_eq {n d : ℕ} (hn : 1 ≤ n) (a : Fin n) (K k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) (hv : UnitV v) (κ : KeyRK k d) :
    fullF d (2 * d * k) a K k t v κ = wRK (surrRK n K t v) d v κ := by
  rw [weight_formula hn a K t ht v hv κ]
  have hR := rep_Q (D := 2 * d * k) a v κ
  simp only [fullF, WF]
  congr 2
  apply Finset.sum_congr rfl
  intro μ _
  have := hR μ
  simp only at this
  rw [this]
  rfl

end BstLean.Part56.MomProg
