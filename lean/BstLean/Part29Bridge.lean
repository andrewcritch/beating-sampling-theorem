import BstLean.Part29Parity
import BstLean.Part29Bessel
import BstLean.Part29GramRaw

/-!
# Part 29, layer L4: bridges for the final assembly

(1) The multilinear monomials `x_S` are an orthogonal family under `SphereParity`. (2) With (1),
`parity_coeff` and `var_ge_bessel`, the variance of `f(m(x))` is at least `w · Σ_S coeffS²`, pointwise in
`m` (the parity floor). (The identification `coeffS = coefC` waits for `Part29Covariance.lean`, which defines `coefC`.)
-/

namespace BstLean.Part29

open MeasureTheory

variable {n : ℕ}

/-- The multilinear monomial of a four-subset, over its sorted enumeration. -/
noncomputable def monoS (S : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  if hS : S.card = 4 then ∏ s, x (S.orderEmbOfFin hS s) else 0

theorem monoS_mean (μ : Measure (Fin n → ℝ)) (w : ℝ) (hμ : SphereParity n μ w)
    (S : Finset (Fin n)) (hS : S.card = 4) : ∫ x, monoS S x ∂μ = 0 := by
  classical
  have hi := (S.orderEmbOfFin hS).injective
  have hc : (Finset.univ.filter (fun s => S.orderEmbOfFin hS s =
      S.orderEmbOfFin hS 0)).card = 1 := by
    have he : Finset.univ.filter (fun s => S.orderEmbOfFin hS s =
        S.orderEmbOfFin hS 0) = {0} := by
      ext s
      simp [hi.eq_iff]
    rw [he]
    simp
  simpa only [monoS, dite_eq_left hS] using
    hμ.parity 4 (by omega) (S.orderEmbOfFin hS)
      ⟨S.orderEmbOfFin hS 0, by rw [hc]; decide⟩

theorem monoS_orth (μ : Measure (Fin n → ℝ)) (w : ℝ) (hμ : SphereParity n μ w)
    (S T : Finset (Fin n)) (hS : S.card = 4) (hT : T.card = 4) (hST : S ≠ T) :
    ∫ x, monoS S x * monoS T x ∂μ = 0 := by
  classical
  have hn : ¬ S ⊆ T := by
    intro h
    exact hST (Finset.eq_of_subset_of_card_le h (by omega))
  obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hn
  have hir : i ∈ Set.range (S.orderEmbOfFin hS) := by
    rw [Finset.range_orderEmbOfFin]
    exact hiS
  obtain ⟨a, ha⟩ := hir
  have hs := (S.orderEmbOfFin hS).injective
  have ht : ∀ b, T.orderEmbOfFin hT b ≠ i := by
    intro b hb
    exact hiT (hb ▸ T.orderEmbOfFin_mem hT b)
  have hc : (Finset.univ.filter (fun b =>
      Fin.append (S.orderEmbOfFin hS) (T.orderEmbOfFin hT) b = i)).card = 1 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have ht' : ∀ b, T.orderEmbOfFin hT b ≠ S.orderEmbOfFin hS a := by
      simpa only [ha] using ht
    simp [← ha, hs.eq_iff, ht']
  have hp := hμ.parity 8 (by omega)
    (Fin.append (S.orderEmbOfFin hS) (T.orderEmbOfFin hT))
    ⟨i, by rw [hc]; decide⟩
  have happ (x : Fin n → ℝ) :
      (∏ b, x (Fin.append (S.orderEmbOfFin hS) (T.orderEmbOfFin hT) b)) =
        (∏ b, x (S.orderEmbOfFin hS b)) * ∏ b, x (T.orderEmbOfFin hT b) := by
    rw [Fin.prod_univ_add (a := 4) (b := 4)]
    simp only [Fin.append_left, Fin.append_right]
  simpa only [monoS, dite_eq_left hS, dite_eq_left hT, happ] using hp

theorem monoS_sq (μ : Measure (Fin n → ℝ)) (w : ℝ) (hμ : SphereParity n μ w)
    (S : Finset (Fin n)) (hS : S.card = 4) : ∫ x, monoS S x ^ 2 ∂μ = w := by
  classical
  simpa only [monoS, dite_eq_left hS, Finset.prod_pow] using
    hμ.square (S.orderEmbOfFin hS) (S.orderEmbOfFin hS).injective

/-- **The parity floor, pointwise in `m`.** -/
theorem var_ge_parity (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (w : ℝ) (hw : 0 < w)
    (hμ : SphereParity n μ w) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hint : Integrable (fun x => funF f0 g F (mapM c L Q x) ^ 2) μ)
    (hint1 : Integrable (fun x => funF f0 g F (mapM c L Q x)) μ) :
    w * ∑ S ∈ Finset.univ.powersetCard 4,
        (if hS : S.card = 4 then coeffS F Q (S.orderEmbOfFin hS) else 0) ^ 2 ≤
      ∫ x, (funF f0 g F (mapM c L Q x) - ∫ x', funF f0 g F (mapM c L Q x') ∂μ) ^ 2 ∂μ := by
  classical
  let A := Finset.univ.powersetCard 4 (α := Fin n)
  let φ : A → (Fin n → ℝ) → ℝ := fun S => monoS S.val
  have hcard (S : A) : S.val.card = 4 := (Finset.mem_powersetCard.mp S.property).2
  have hφ (S : A) : Integrable (φ S) μ := by
    change Integrable (fun x => monoS S.val x) μ
    simpa only [monoS, dite_eq_left (hcard S)] using
      hμ.integ 4 (by omega) (S.val.orderEmbOfFin (hcard S))
  have hφ2 (S T : A) : Integrable (fun x => φ S x * φ T x) μ := by
    have hp := hμ.integ 8 (by omega)
      (Fin.append (S.val.orderEmbOfFin (hcard S)) (T.val.orderEmbOfFin (hcard T)))
    have happ (x : Fin n → ℝ) :
        (∏ b, x (Fin.append (S.val.orderEmbOfFin (hcard S))
          (T.val.orderEmbOfFin (hcard T)) b)) =
          (∏ b, x (S.val.orderEmbOfFin (hcard S) b)) *
            ∏ b, x (T.val.orderEmbOfFin (hcard T) b) := by
      rw [Fin.prod_univ_add (a := 4) (b := 4)]
      simp only [Fin.append_left, Fin.append_right]
    simpa only [φ, monoS, dite_eq_left (hcard S), dite_eq_left (hcard T), happ] using hp
  have hhφ (S : A) : Integrable (fun x => funF f0 g F (mapM c L Q x) * φ S x) μ := by
    have hp2 : Integrable (fun x => φ S x ^ 2) μ := by
      simpa only [pow_two] using hφ2 S S
    exact ((memLp_two_iff_integrable_sq hint1.aestronglyMeasurable).mpr hint).integrable_mul
      ((memLp_two_iff_integrable_sq (hφ S).aestronglyMeasurable).mpr hp2)
  have hb := var_ge_bessel μ (fun x => funF f0 g F (mapM c L Q x)) φ w hw
    hint hint1 hφ2 hhφ hφ
    (fun S => monoS_mean μ w hμ S.val (hcard S))
    (fun S T hST => monoS_orth μ w hμ S.val T.val (hcard S) (hcard T)
      (fun h => hST (Subtype.ext h)))
    (fun S => monoS_sq μ w hμ S.val (hcard S))
  have hcov (S : A) :
      (∫ x, funF f0 g F (mapM c L Q x) * φ S x ∂μ) =
        w * coeffS F Q (S.val.orderEmbOfFin (hcard S)) := by
    simpa only [φ, monoS, dite_eq_left (hcard S)] using
      parity_coeff μ w hμ c L Q f0 g F (S.val.orderEmbOfFin (hcard S))
        (S.val.orderEmbOfFin (hcard S)).injective
  simp_rw [hcov] at hb
  have halg (a : ℝ) : (w * a) ^ 2 / w = w * a ^ 2 := by
    field_simp [ne_of_gt hw]
  simp_rw [halg] at hb
  rw [← Finset.mul_sum] at hb
  convert hb using 1
  congr 1
  rw [Finset.sum_coe_sort_eq_attach]
  rw [← Finset.sum_attach A (fun S =>
    (if hS : S.card = 4 then coeffS F Q (S.orderEmbOfFin hS) else 0) ^ 2)]
  apply Finset.sum_congr rfl
  intro S _
  simp only [dite_eq_left (hcard S)]

end BstLean.Part29
