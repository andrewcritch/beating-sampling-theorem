import BstLean.Part223RadialSquare
import BstLean.Part223ExactRadius
import BstLean.Part172Node

/-! Spherical variance and moments for squares, through a proved degree-one extension. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 unitF53)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq)
open BstLean.Part161 (momN)
open BstLean.Part162

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H : (ι → ℝ) → ℝ} {L : ℝ}

lemma radialSquare_tangent_ae (hL0 : 0 ≤ L) (hL : EuLip H L)
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v) :
    ∀ᵐ v ∂stdGauss ι,
      gradSq (radialSquare H) v - radialSquare H (unitF53 v) ^ 2 =
        4 * H (unitF53 v) ^ 2 * (gradSq H v - H (unitF53 v) ^ 2) := by
  have hz : ∀ᵐ v ∂stdGauss ι, v ≠ 0 := by
    have h0 := BstLean.Part148.stdGauss_ac
      (measure_singleton (μ := (volume : Measure (ι → ℝ))) (0 : ι → ℝ))
    rw [ae_iff]
    simpa using h0
  filter_upwards [hz, hL.ae_diff hL0] with v hv hd
  exact radialSquare_tangent hh hv hd

/-- The square has the spherical Poincare constant, without a degree-two premise. -/
theorem squared_sphere_variance (hL0 : 0 ≤ L) (hL : EuLip H L)
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v) :
    ((Fintype.card ι : ℝ) - 1) *
        (∫ v, (H (unitF53 v) ^ 2 - ∫ w, H (unitF53 w) ^ 2 ∂stdGauss ι) ^ 2
          ∂stdGauss ι) ≤
      ∫ v, 4 * H (unitF53 v) ^ 2 * (gradSq H v - H (unitF53 v) ^ 2)
        ∂stdGauss ι := by
  have h := ls_var (by positivity : 0 ≤ 3 * L ^ 2) (radialSquare_lip hL0 hL hh)
    (radialSquare_hom hh)
  rw [integral_congr_ae (radialSquare_tangent_ae hL0 hL hh)] at h
  simpa only [radialSquare_unit hh] using h

/-- The centred moment of the square uses the actual squared tangential gradient. -/
theorem squared_sphere_moment (hL0 : 0 ≤ L) (hL : EuLip H L)
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v)
    {q : ℕ} (hq : 1 ≤ q) (hqdim : 2 * q < Fintype.card ι) :
    momN (stdGauss ι) (2 * q)
        (fun v => H (unitF53 v) ^ 2 - ∫ w, H (unitF53 w) ^ 2 ∂stdGauss ι) ≤
      cLS q * (momN (stdGauss ι) (2 * q)
        (fun v => sqrt (4 * H (unitF53 v) ^ 2 *
          (gradSq H v - H (unitF53 v) ^ 2))) *
            (((Fintype.card ι : ℝ) - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) := by
  have h := ls_mom_sharp (by positivity : 0 ≤ 3 * L ^ 2)
    (radialSquare_lip hL0 hL hh) (radialSquare_hom hh) hq hqdim
  have he : momN (stdGauss ι) (2 * q)
      (fun v => sqrt (gradSq (radialSquare H) v - radialSquare H (unitF53 v) ^ 2)) =
      momN (stdGauss ι) (2 * q)
        (fun v => sqrt (4 * H (unitF53 v) ^ 2 *
          (gradSq H v - H (unitF53 v) ^ 2))) := by
    unfold momN
    congr 1
    apply integral_congr_ae
    filter_upwards [radialSquare_tangent_ae hL0 hL hh] using fun v hv => by rw [hv]
  rw [he] at h
  simpa only [radialSquare_unit hh] using h

/-- The centred moment of the square uses the actual squared tangential gradient. -/
theorem squared_sphere_eight_exact (hL0 : 0 ≤ L) (hL : EuLip H L)
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v)
    (hqdim : 8 < Fintype.card ι) :
    momN (stdGauss ι) 8
        (fun v => H (unitF53 v) ^ 2 - ∫ w, H (unitF53 w) ^ 2 ∂stdGauss ι) ≤
      cLS 4 * (momN (stdGauss ι) 8
        (fun v => sqrt (4 * H (unitF53 v) ^ 2 *
          (gradSq H v - H (unitF53 v) ^ 2))) *
            radiusFactor8 (Fintype.card ι)) := by
  have h := ls_mom_radius (by positivity : 0 ≤ 3 * L ^ 2)
    (radialSquare_lip hL0 hL hh) (radialSquare_hom hh) (q := 4) (by norm_num) hqdim
    (R := radiusFactor8 (Fintype.card ι))
    (Real.rpow_nonneg (inverseRadius8_pos hqdim).le _)
    (fun ε => by simpa only [show 2 * 4 = 8 from rfl, radiusFactor8_pow hqdim]
      using trunc_invRad_eight hqdim ε)
  have he : momN (stdGauss ι) 8
      (fun v => sqrt (gradSq (radialSquare H) v - radialSquare H (unitF53 v) ^ 2)) =
      momN (stdGauss ι) 8
        (fun v => sqrt (4 * H (unitF53 v) ^ 2 *
          (gradSq H v - H (unitF53 v) ^ 2))) := by
    unfold momN
    congr 1
    apply integral_congr_ae
    filter_upwards [radialSquare_tangent_ae hL0 hL hh] using fun v hv => by rw [hv]
  norm_num only [Nat.reduceMul] at h
  rw [he] at h
  simpa only [radialSquare_unit hh] using h

#print axioms squared_sphere_eight_exact

#print axioms radialSquare_tangent_ae
#print axioms squared_sphere_variance
#print axioms squared_sphere_moment

end BstLean.Part223

namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq)
open BstLean.Part157 (Ret)
open BstLean.Part161 (xLat momN)
open BstLean.Part162

variable {n : ℕ} {Φ : (Fin n → ℝ) → ℝ} {L : ℝ}

lemma latitudeLift_lip (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1)
    (hL0 : 0 ≤ L) (hL : EuLip Φ L) : EuLip (fun v => Φ (xLatH c s v)) L := by
  intro v w
  exact (hL _ _).trans (mul_le_mul_of_nonneg_left
    (sqrt_le_sqrt (xLatH_dist hn c hs v w)) hL0)

lemma latitudeLift_hom (c : Ret n) (s : ℝ)
    (hh : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x)
    (t : ℝ) (v : Fin (n - 1) → ℝ) (ht : 0 < t) :
    Φ (xLatH c s (t • v)) = t * Φ (xLatH c s v) := by
  rw [xLatH_smul c s ht, hh _ _ ht]

lemma latitudeLift_unit_ae (hn : 2 ≤ n) (c : Ret n) (s : ℝ) :
    ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      Φ (xLatH c s (unitF53 v)) = Φ (xLat c s (unitF53 v)) := by
  have hz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 := BstLean.Part168.stdGauss_zero (by omega : 1 ≤ n - 1)
    rw [ae_iff]
    simpa using h0
  filter_upwards [hz] with v hv
  rw [xLatH_eq, radF_unitF hv, unitF_unitF hv, one_smul]

/-- The variance estimate applies directly to the square on a latitude. -/
theorem squared_latitude_variance (hn : 3 ≤ n) (c : Ret n) {s : ℝ}
    (hs : s ^ 2 ≤ 1) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hh : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) :
    ((n : ℝ) - 2) * (∫ v, (Φ (xLat c s (unitF53 v)) ^ 2 -
        ∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2
          ∂stdGauss (Fin (n - 1))) ≤
      ∫ v, 4 * Φ (xLat c s (unitF53 v)) ^ 2 * tanSq Φ c s v
        ∂stdGauss (Fin (n - 1)) := by
  haveI : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have h := squared_sphere_variance hL0 (latitudeLift_lip (by omega) c hs hL0 hL)
    (latitudeLift_hom c s hh)
  have he := latitudeLift_unit_ae (Φ := Φ) (by omega) c s
  have hm := integral_congr_ae (he.mono fun v hv => congrArg (fun z : ℝ => z ^ 2) hv)
  rw [hm] at h
  have hleft := integral_congr_ae (he.mono fun v hv => (by
    rw [hv] :
      (Φ (xLatH c s (unitF53 v)) ^ 2 -
        ∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 =
      (Φ (xLat c s (unitF53 v)) ^ 2 -
        ∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2))
  have hright := integral_congr_ae (he.mono fun v hv => (by
    simp only [hv, tanSq] :
      4 * Φ (xLatH c s (unitF53 v)) ^ 2 *
        (gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLatH c s (unitF53 v)) ^ 2) =
      4 * Φ (xLat c s (unitF53 v)) ^ 2 * tanSq Φ c s v))
  rw [hleft, hright, Fintype.card_fin, Nat.cast_sub (by omega)] at h
  norm_num only [Nat.cast_one] at h
  convert h using 1 <;> ring

#print axioms squared_latitude_variance

lemma momN_congr_ae' {V : Type*} [MeasurableSpace V] (μ : Measure V) (k : ℕ)
    {f g : V → ℝ} (h : f =ᵐ[μ] g) : momN μ k f = momN μ k g := by
  unfold momN
  congr 1
  exact integral_congr_ae (h.mono fun _ hx => congrArg (fun z : ℝ => |z| ^ k) hx)

/-- The order-eight bound uses the installed spherical factor `(n-9)^(-1/2)`. -/
theorem squared_latitude_eight (hn : 10 ≤ n) (c : Ret n) {s : ℝ}
    (hs : s ^ 2 ≤ 1) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hh : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) :
    momN (stdGauss (Fin (n - 1))) 8
      (fun v => Φ (xLat c s (unitF53 v)) ^ 2 -
        ∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1))) ≤
      cLS 4 * (momN (stdGauss (Fin (n - 1))) 8
        (fun v => sqrt (4 * Φ (xLat c s (unitF53 v)) ^ 2 * tanSq Φ c s v)) *
          (((n : ℝ) - 9)⁻¹) ^ ((2 : ℝ)⁻¹)) := by
  haveI : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have h := squared_sphere_moment hL0 (latitudeLift_lip (by omega) c hs hL0 hL)
    (latitudeLift_hom c s hh) (q := 4) (by norm_num) (by simp; omega)
  have he := latitudeLift_unit_ae (Φ := Φ) (by omega) c s
  have hm := integral_congr_ae (he.mono fun v hv => congrArg (fun z : ℝ => z ^ 2) hv)
  rw [hm] at h
  have hleft := momN_congr_ae' (stdGauss (Fin (n - 1))) 8
    (he.mono fun v hv => (by rw [hv] :
      Φ (xLatH c s (unitF53 v)) ^ 2 -
        (∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1))) =
      Φ (xLat c s (unitF53 v)) ^ 2 -
        (∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1)))))
  have hright := momN_congr_ae' (stdGauss (Fin (n - 1))) 8
    (he.mono fun v hv => (by simp only [hv, tanSq] :
      sqrt (4 * Φ (xLatH c s (unitF53 v)) ^ 2 *
        (gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLatH c s (unitF53 v)) ^ 2)) =
      sqrt (4 * Φ (xLat c s (unitF53 v)) ^ 2 * tanSq Φ c s v)))
  norm_num only [Nat.reduceMul] at h
  rw [hleft, hright, Fintype.card_fin, Nat.cast_sub (by omega)] at h
  norm_num only [Nat.cast_one] at h
  convert h using 1 <;> ring

/-- The order-eight bound retains the exact inverse radial product. -/
theorem squared_latitude_eight_exact (hn : 10 ≤ n) (c : Ret n) {s : ℝ}
    (hs : s ^ 2 ≤ 1) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hh : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) :
    momN (stdGauss (Fin (n - 1))) 8
      (fun v => Φ (xLat c s (unitF53 v)) ^ 2 -
        ∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1))) ≤
      cLS 4 * (momN (stdGauss (Fin (n - 1))) 8
        (fun v => sqrt (4 * Φ (xLat c s (unitF53 v)) ^ 2 * tanSq Φ c s v)) *
          radiusFactor8 (n - 1)) := by
  haveI : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have h := squared_sphere_eight_exact hL0 (latitudeLift_lip (by omega) c hs hL0 hL)
    (latitudeLift_hom c s hh) (by simp; omega)
  have he := latitudeLift_unit_ae (Φ := Φ) (by omega) c s
  have hm := integral_congr_ae (he.mono fun v hv => congrArg (fun z : ℝ => z ^ 2) hv)
  rw [hm] at h
  have hleft := momN_congr_ae' (stdGauss (Fin (n - 1))) 8
    (he.mono fun v hv => (by rw [hv] :
      Φ (xLatH c s (unitF53 v)) ^ 2 -
        (∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1))) =
      Φ (xLat c s (unitF53 v)) ^ 2 -
        (∫ w, Φ (xLat c s (unitF53 w)) ^ 2 ∂stdGauss (Fin (n - 1)))))
  have hright := momN_congr_ae' (stdGauss (Fin (n - 1))) 8
    (he.mono fun v hv => (by simp only [hv, tanSq] :
      sqrt (4 * Φ (xLatH c s (unitF53 v)) ^ 2 *
        (gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLatH c s (unitF53 v)) ^ 2)) =
      sqrt (4 * Φ (xLat c s (unitF53 v)) ^ 2 * tanSq Φ c s v)))
  norm_num only [Nat.reduceMul] at h
  simpa only [hleft, hright, Fintype.card_fin] using h

#print axioms squared_latitude_eight_exact

#print axioms squared_latitude_eight
end BstLean.Part223
