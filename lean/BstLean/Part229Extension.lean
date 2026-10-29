import BstLean.Part229Cap
import BstLean.Part153SL

/-! A concrete extension of a capped scalar test from the unit sphere. -/
namespace BstLean.Part229
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part188
open BstLean.Part148 (EuLip)

noncomputable def cappedExtension {n : ℕ} (a d : ℝ)
    (f z : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  weight a d (f (cut 1 x)) * z (cut 1 x)

noncomputable def extensionConstant (d R S Lf Lz : ℝ) : ℝ :=
  (√d)⁻¹ * Lz + S * (2 * R / (d * √d)) * Lf

lemma extensionConstant_nonneg {d R S Lf Lz : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) (hS : 0 ≤ S) (hf : 0 ≤ Lf) (hz : 0 ≤ Lz) :
    0 ≤ extensionConstant d R S Lf Lz := by
  unfold extensionConstant
  positivity

lemma cappedExtension_on_sphere {n : ℕ} (a d : ℝ)
    (f z : (Fin n → ℝ) → ℝ) {x : Fin n → ℝ} (hx : normSq x = 1) :
    cappedExtension a d f z x = weight a d (f x) * z x := by
  simp only [cappedExtension, cut_one_unit_sl hx]

theorem cappedExtension_lip {n : ℕ} {a d R S Lf Lz : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) (hS : 0 ≤ S) (hLf : 0 ≤ Lf) (hLz : 0 ≤ Lz)
    (f z : (Fin n → ℝ) → ℝ) (hf : EuLip f Lf) (hz : EuLip z Lz)
    (hfb : ∀ x, nrm x ≤ 1 → |f x| ≤ R)
    (hzb : ∀ x, nrm x ≤ 1 → |z x| ≤ S) :
    EuLip (cappedExtension a d f z) (extensionConstant d R S Lf Lz) := by
  intro x y
  have hN := nrm_nonneg (x - y)
  change |weight a d (f (cut 1 x)) * z (cut 1 x) -
    weight a d (f (cut 1 y)) * z (cut 1 y)| ≤ _
  have hfx : |f (cut 1 x)| ≤ R := hfb _ (nrm_cut_le_sl x)
  have hfy : |f (cut 1 y)| ≤ R := hfb _ (nrm_cut_le_sl y)
  have hzy : |z (cut 1 y)| ≤ S := hzb _ (nrm_cut_le_sl y)
  have hfxy : |f (cut 1 x) - f (cut 1 y)| ≤ Lf * nrm (x - y) :=
    (hf _ _).trans (mul_le_mul_of_nonneg_left (nrm_cut_sub_le_sl x y) hLf)
  have hzxy : |z (cut 1 x) - z (cut 1 y)| ≤ Lz * nrm (x - y) :=
    (hz _ _).trans (mul_le_mul_of_nonneg_left (nrm_cut_sub_le_sl x y) hLz)
  have hwxy : |weight a d (f (cut 1 x)) - weight a d (f (cut 1 y))| ≤
      (2 * R / (d * √d)) * (Lf * nrm (x - y)) :=
    (weight_sub_bounded hd hfx hfy).trans
      (mul_le_mul_of_nonneg_left hfxy (by positivity))
  have hw : |weight a d (f (cut 1 x))| ≤ (√d)⁻¹ := by
    rw [abs_of_nonneg (show 0 ≤ weight a d (f (cut 1 x)) from Real.sqrt_nonneg _)]
    exact weight_le hd
  calc
    _ = |weight a d (f (cut 1 x)) * (z (cut 1 x) - z (cut 1 y)) +
        (weight a d (f (cut 1 x)) - weight a d (f (cut 1 y))) * z (cut 1 y)| := by
      congr 1; ring
    _ ≤ |weight a d (f (cut 1 x))| * |z (cut 1 x) - z (cut 1 y)| +
        |weight a d (f (cut 1 x)) - weight a d (f (cut 1 y))| * |z (cut 1 y)| := by
      simpa only [abs_mul] using abs_add_le
        (weight a d (f (cut 1 x)) * (z (cut 1 x) - z (cut 1 y)))
        ((weight a d (f (cut 1 x)) - weight a d (f (cut 1 y))) * z (cut 1 y))
    _ ≤ (√d)⁻¹ * (Lz * nrm (x - y)) +
        ((2 * R / (d * √d)) * (Lf * nrm (x - y))) * S := by
      exact add_le_add (mul_le_mul hw hzxy (abs_nonneg _) (by positivity))
        (mul_le_mul hwxy hzy (abs_nonneg _) (by positivity))
    _ = _ := by unfold extensionConstant nrm normSq; simp only [Pi.sub_apply]; ring

end BstLean.Part229
