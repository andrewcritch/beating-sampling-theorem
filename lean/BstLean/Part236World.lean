import BstLean.Part236RetainedMoments
import BstLean.Part236Master
import BstLean.Part232Transfer

/-! RF supplies the actual World frame on each product cell and integrates its moments. -/
namespace BstLean.Part236
open MeasureTheory Real Set
open BstLean.Part156 BstLean.Part130 BstLean.Part134 BstLean.Part136
open BstLean.Part157 BstLean.Part159 BstLean.Part192 BstLean.Part203
open BstLean.Part227 BstLean.Part232

def worldProductCell {n : ℕ} (D : Design n) (E : Set (Ret n))
    (Rcov : RadiusCover) (Scov : FrameCover) (S : WHid n → ℝ) (i j : ℕ) : Set (Ret n) :=
  E ∩ {x | radiusCell Rcov.h i (HbarW D x) ∧ radiusCell Scov.h j (S x.1.1)}

theorem product_cell_frame {n : ℕ} (hn : 4096 ≤ n) (D : Design n)
    (hD : D.bW = bWp) {Xc dT eB e d : ℝ}
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 ≤ dT) (hdT : dT ≤ 1 / 400000)
    (c : FrameCertificate n (4 / 100) (4 / 10000) Xc dT eB)
    (he : 0 < e) (hd : 0 < d) {E : Set (Ret n)}
    (hbase : E ⊆ Hof (hidden n (4 / 100) (4 / 10000) Xc dT eB))
    (Rcov : RadiusCover) (Scov : FrameCover) (i j : ℕ) :
    FRAME_W_hyp D.toCentres ((frameBase c e d + Scov.h (j + 1)) / n)
      (worldProductCell D E Rcov Scov (frameError c e) i j) := by
  intro x hx w
  have hf := pointwise_frame hn hXc hdT0 hdT c he hd (hbase hx.1) w
  have hupper : frameError c e x.1.1 ≤ Scov.h (j + 1) := hx.2.2.2
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmul : (frameBase c e d + frameError c e x.1.1) / (n : ℝ) * ∑ j, w j ^ 2 ≤
      (frameBase c e d + Scov.h (j + 1)) / (n : ℝ) * ∑ j, w j ^ 2 :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (add_le_add le_rfl hupper) hn'.le)
      (Finset.sum_nonneg (fun k _ => sq_nonneg (w k)))
  rw [hD]
  exact hf.trans hmul

/-- RF replaces the fixed World cutoff payment in the retained classifier ledger. -/
theorem world_rf {n : ℕ} (hn : 4096 ≤ n) {P : Program n} {w : WorldParameters}
    (W : WorldPackage P w) (hD : P.design.bW = bWp) (t : ℝ) (k : ℕ)
    {E : Set (Ret n)} (hE : MeasurableSet E) (hsub : E ⊆ Hof W.hidden)
    {Xc dT eB e d : ℝ} (hXc : Xc ≤ 3 / 4)
    (hdT0 : 0 ≤ dT) (hdT : dT ≤ 1 / 400000)
    (c : FrameCertificate n (4 / 100) (4 / 10000) Xc dT eB)
    (he : 0 < e) (hd : 0 < d)
    (hbase : E ⊆ Hof (hidden n (4 / 100) (4 / 10000) Xc dT eB))
    (Rcov : RadiusCover) (Scov : FrameCover)
    (hlast : Scov.maximum = 25 * coeffK c e + 2500 * coeffD c e)
    {f a hA ds c₀ c₁ q r δs δret : ℝ}
    (hc : 0 < frameBase c e d) (hf : 0 < f) (ha : 0 < a)
    (hhA : 0 ≤ hA) (hds : 0 ≤ ds) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hq : 0 < q) (hr : 0 ≤ r) (hδs : 0 ≤ δs)
    (cert : ∀ i j, Option (EndCertificate n (frameBase c e d + Scov.h (j + 1)) f a
      (hA + ds) (Rcov.h (i + 1))))
    (hline : ∀ i < Rcov.K, ∀ j < Scov.K,
      cellPayment (cert i j) ≤ c₀ + c₁ * Rcov.h i ^ 2 + framePrice q r (Scov.h j))
    (hterminal : 1 ≤ c₀ + c₁ * Rcov.h Rcov.K ^ 2)
    (hFA : ∀ i < Rcov.K, ∀ j < Scov.K, (cert i j).isSome →
      FRAME_A_hyp P.design (f / n)
        (worldProductCell P.design E Rcov Scov (frameError c e) i j))
    (hroot : ∀ x ∈ E, |√(QStand P.design t x) - √(qTilde P.design t x)| ≤ hA)
    (hsamp : ∀ x ∈ E, (sampMeas k n).real
      {s | ds < |√(hitFrac (hits P.design t k) (x, s)) - √(qTilde P.design t x)|} ≤ δs)
    (hcomp : (retDist P.design.toCentres).real Eᶜ ≤ δret) :
    ((retDist P.design.toCentres).prod (((resW n).prod (resA n)).prod (sampMeas k n))).real
      (programFailure a (fun x => pRes P.design.toCentres t x.1 x.2)
        (hitFrac (hits P.design t k))) ≤
      δret + (c₀ + c₁ * w.moment + q * (372 / 1000 * coeffK c e ^ 2) +
        r * (448 / 1000 * coeffD c e)) + δs := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hK : 0 ≤ coeffK c e := coeffK_nonneg c he
  have hDcoeff : 0 ≤ coeffD c e := coeffD_nonneg c he
  have hm := world_retained_moment W hsub
  have herrors := retained_error_moments hn P.design.toCentres c he E
  have hqt : Measurable (qTilde P.design t) :=
    (measurable_hitFn P.design t).stronglyMeasurable.integral_prod_right'.measurable
  apply rf_end_master (ρ := HbarW P.design)
    (x := fun x : Ret n => coeffK c e * √(yK x.1.1))
    (y := fun x : Ret n => coeffD c e * yD x.1.1)
    (Q := QStand P.design t) (qt := qTilde P.design t)
    (retDist P.design.toCentres) ((resW n).prod (resA n)) (sampMeas k n) hE Rcov Scov
    (fun _ => sqrt_nonneg _) (fun _ => mul_nonneg hK (sqrt_nonneg _))
    (fun x => mul_nonneg hDcoeff (yD_nonneg x.1.1))
    (fun x hx => by
      rw [hlast]
      exact frame_error_max hn c he (hbase hx)) hqt
    (measurable_pRes P.design.toCentres t) (fun _ => pRes_nonneg _ _ _ _)
    (fun _ => pRes_le_one hn1 _ _ _ _) (measurable_hitFrac P.design t k)
    (fun x => by
      unfold hitFrac
      apply div_nonneg _ (Nat.cast_nonneg k)
      apply Finset.sum_nonneg
      intro i _
      rcases hits_01 P.design t k i x with hi | hi <;> simp [hi])
    hn' hc hf ha hhA hds hc₀ hc₁ hq hr hδs cert hm.1 herrors.1 herrors.2.1
    hm.2 herrors.2.2.1 herrors.2.2.2 hline hterminal
    (fun x _ => QStand_mem_01 _ _ x) hroot _ hsamp hcomp
  intro x hx i hi j hj hrc hsc hsome
  have hcc : 0 < frameBase c e d + Scov.h (j + 1) :=
    add_pos_of_pos_of_nonneg hc (Scov.toRadiusCover.nonneg (by omega))
  apply network_free_cpr hn1 P.design t hcc hf (Rcov.nonneg (by omega))
    (product_cell_frame hn P.design hD hXc hdT0 hdT c he hd hbase Rcov Scov i j)
    (hFA i hi j hj hsome) _ x ⟨hx, hrc, hsc⟩
  intro z hz ω hT
  exact (replw_hellinger hn1 P.design z hT).trans hz.2.1.2
end BstLean.Part236
